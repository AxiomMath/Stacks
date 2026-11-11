module

public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingBridge
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.Basis.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# A Leray--Hirsch theorem for the relative de Rham complex

Let `f : X ⟶ Y` be a proper smooth morphism of schemes, let `n_1, …, n_N` be nonnegative
integers and let `ξ_i ∈ H^{n_i}_{dR}(X/Y)` be relative de Rham cohomology classes. Each `ξ_i`
determines a morphism `𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` in `D(𝒪_Y)`, and together they give

`a : ⨁_{i=1}^N 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}`.

If for every point `y ∈ Y` the images of `ξ_1, …, ξ_N` in `H^*_{dR}(X_y/κ(y))` form a basis
over `κ(y)`, then `a` is an isomorphism.

The argument is the source's. The cone `C` of `a` is perfect, because the source and the target
are; the fibrewise hypothesis says that the derived fibre of `C` vanishes at every point; and a
pseudo-coherent complex over a local ring whose derived fibre has no cohomology is zero, by the
minimal-representative theorem. So the derived stalk of `C` vanishes at every point, hence the
derived stalk of `a` is invertible at every point, hence `a` is invertible.

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImage`: `Rf_*Ω^•_{X/Y}` as an object of the
  unbounded derived category of `𝒪_Y`-modules.
* `AlgebraicGeometry.DeRhamLerayHirsch.structureSheafShift` and
  `AlgebraicGeometry.DeRhamLerayHirsch.shiftedStructureSum`: the objects `𝒪_Y[-m]` and
  `⨁_{i=1}^N 𝒪_Y[-n_i]` of `D(𝒪_Y)`.
* `AlgebraicGeometry.DeRhamLerayHirsch.fibreDeRhamCohomology`,
  `AlgebraicGeometry.DeRhamLerayHirsch.fibreDeRhamModule` and
  `AlgebraicGeometry.DeRhamLerayHirsch.fibreRestriction`: the de Rham cohomology of the fibre
  `X_y`, its `κ(y)`-module realization, and the restriction of a relative class to the fibre.
* `AlgebraicGeometry.DeRhamLerayHirsch.LerayHirschInput` and
  `AlgebraicGeometry.DeRhamLerayHirsch.LerayHirschFibreData`: **the carried inputs**, listed in
  the implementation notes below.
* `AlgebraicGeometry.DeRhamLerayHirsch.classSumMorphism`: **the morphism `a` of the statement**,
  the direct sum over `i` of the morphisms attached to the classes `ξ_i`.
* `AlgebraicGeometry.DeRhamLerayHirsch.HasFibrewiseBasis`: **the fibrewise basis hypothesis**.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.isZero_of_forall_isZero_residueFibreHomology`: a
  pseudo-coherent object of `D(R)`, for `R` a local ring, whose derived fibre `K ⊗ᴸ_R κ` has
  vanishing cohomology in every degree is zero.
* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_of_forall_isZero_derivedFibreHomology`: a morphism
  of `D(𝒪_Y)` sitting in a distinguished triangle whose third vertex has pseudo-coherent derived
  stalks and vanishing derived fibres is an isomorphism.
* `AlgebraicGeometry.DeRhamLerayHirsch.isPerfect_cone`: [Stacks, Tag 08CR] for the cone of the
  Leray--Hirsch morphism.

## Implementation notes

**The descent step, which is what is proved.** The two halves of the source's argument that are
new here are `isZero_of_forall_isZero_residueFibreHomology` and
`isIso_of_forall_isZero_derivedFibreHomology`. The first is the Nakayama step: the
minimal-representative theorem over a local ring ([Stacks, Tag 0BCC],
`StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing`) produces a
representative whose term in degree `i` is free of rank `dim_κ H^i(K ⊗ᴸ κ)`, so vanishing of the
derived fibre makes every term a zero module and the representative a zero complex. This is the
local-ring form of [Stacks, Tag 0BCD], which is what a stalk needs: [Stacks, Tag 0BCD] itself is
stated at a prime of a global ring and produces a representative over a principal localization,
which would then have to be glued. The second half is the passage from the stalks to the sheaf,
`Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso`, read in the local-ring
spelling of the stalk through `AlgebraicGeometry.isIso_derivedStalkFunctor_map_iff`; the stalk
functor is exact, so it carries the distinguished triangle of the statement to a distinguished
triangle, and the vanishing of the third vertex there is invertibility of the first map.

**The derived fibre.** `derivedFibreHomology K y i` is the degree-`i` cohomology of
`K_y ⊗ᴸ_{𝒪_{Y,y}} κ(y)`: the derived stalk at `y`, over the local ring `𝒪_{Y,y}`, followed by
the canonical total derived extension of scalars along the residue map. This is the derived
fibre, taken in the one spelling in which the minimal-representative theorem is available.

**The carried inputs.** Four pieces of the source's proof are not available in the library and
are carried as named fields rather than reconstructed.

* `LerayHirschInput.classMorphism`, the identification
  `H^m_{dR}(X/Y) = Hom_{D(𝒪_Y)}(𝒪_Y[-m], Rf_*Ω^•_{X/Y})` which turns a de Rham class into a
  morphism of `D(𝒪_Y)`. The library constructs the differential graded avatar
  `Ω^• ⟶ Ω^•[m]` of [Stacks, Tag 0FU7]
  (`AlgebraicGeometry.SheafOfModules.deRhamClassMorphism`), and no comparison between that and
  the direct image is made.
* `LerayHirschInput.isPerfect`, perfectness of `Rf_*Ω^•_{X/Y}`: the perfectness half of
  [Stacks, Tag 0FM0] *for the complex*. The library has it for the sheaves `Ω^p_{X/Y}` only
  (`AlgebraicGeometry.ProperSmoothDeRham.isPerfect_derivedPushforward_relativeDifferentialForms`),
  and the implementation notes of that file record why the passage to the complex is unavailable
  there: the truncation triangles of the de Rham complex are not at hand in the spelling its
  direct image is taken at.
* `LerayHirschInput.fibreRealization`, the comparison of the two realizations of the de Rham
  cohomology of the fibre. The pullback map `Scheme.Hom.deRhamCohomologyPullback`, which is how
  a class is restricted to a fibre, is stated for the abelian-sheaf realization
  `Scheme.Hom.deRhamCohomology`, while the `κ(y)`-vector space structure over which a basis can
  be spoken of comes from `Scheme.Hom.deRhamCohomologyBaseModule`; the two realizations are not
  compared in the library.
* `LerayHirschFibreData.isZero_derivedFibre`, which is carried **as an implication from the
  fibrewise basis hypothesis** and not as a bare assumption: that a fibrewise basis forces the
  derived fibres of the cone to vanish. This is the base-change half of [Stacks, Tag 0FM0] for
  the complex, together with the identification of `Rf_*Ω^•_{X/Y} ⊗ᴸ κ(y)` with
  `RΓ(X_y, Ω^•_{X_y/κ(y)})`; the library carries that half for `Ω^p` only, and only in the
  tensor form of [Stacks, Tag 0B91]. The cone itself is carried as data in the same structure,
  pinned down by the requirement that its triangle be distinguished, since `D(𝒪_Y)` offers only
  the existence of a cone and not a chosen one.

What is **not** assumed is the passage from the fibrewise statement to the global one. That is
the content of [Stacks, Tag 0FMP] and it is proved here.

## References

* [Stacks Project, Tag 0FMP](https://stacks.math.columbia.edu/tag/0FMP)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### A Nakayama criterion over a local ring -/

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The degree-`i` cohomology of the derived fibre `K ⊗ᴸ_R κ` of an object of `D(R)` at the
maximal ideal of a local ring `R`. -/
abbrev residueFibreHomology (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    ModuleCat.{u} (IsLocalRing.ResidueField R) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (IsLocalRing.ResidueField R)) i).obj
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (IsLocalRing.residue R)).functor.obj K)

/-- **A pseudo-coherent object of `D(R)` over a local ring whose derived fibre has no cohomology
is zero.** The minimal representative of [Stacks, Tag 0BCC] has free terms of rank the fibre
dimensions, so all of its terms are zero modules. -/
theorem isZero_of_forall_isZero_residueFibreHomology (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (h : ∀ i : ℤ, IsZero (residueFibreHomology K i)) :
    IsZero K := by
  obtain ⟨-, -, -, P, -, ⟨hPX, ⟨e⟩⟩, -⟩ :=
    StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing.{u, u} K hK
  have hrank : ∀ i : ℤ,
      Module.finrank (IsLocalRing.ResidueField R) (residueFibreHomology K i) = 0 := by
    intro i
    have : Subsingleton (residueFibreHomology K i) :=
      ModuleCat.isZero_iff_subsingleton.1 (h i)
    exact Module.finrank_zero_of_subsingleton
  have hzero : ∀ i : ℤ, IsZero (P.X i) := by
    intro i
    refine IsZero.of_iso ?_ (hPX i).some
    rw [hrank i]
    exact ModuleCat.isZero_of_subsingleton _
  have hP : IsZero P := by
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.hom_ext _ _ fun i => (hzero i).eq_of_src _ _
  exact (DerivedCategory.Q.map_isZero hP).of_iso e.symm

end LocalRing

/-! ### Invertibility in `D(𝒪_Y)` from the derived fibres -/

section Fibrewise

variable {Y : Scheme.{u}}

/-- The degree-`i` cohomology of the derived fibre of `K` at a point `y` of `Y`: the derived
stalk at `y`, over the local ring `𝒪_{Y,y}`, reduced modulo the maximal ideal. -/
abbrev derivedFibreHomology (K : DerivedCategory Y.Modules) (y : Y) (i : ℤ) :
    ModuleCat.{u} (IsLocalRing.ResidueField (ToType (Y.presheaf.stalk y))) :=
  residueFibreHomology ((AlgebraicGeometry.derivedStalkFunctor y).obj K) i

/-- **A morphism of `D(𝒪_Y)` whose cone has vanishing derived fibres is an isomorphism.** The
cone is required to have pseudo-coherent derived stalks; the Nakayama criterion then makes every
derived stalk of the cone zero, so every derived stalk of the morphism is invertible, and
invertibility in `D(𝒪_Y)` is detected by the derived stalks. -/
theorem isIso_of_forall_isZero_derivedFibreHomology
    {T : Triangle (DerivedCategory Y.Modules)} (hT : T ∈ distTriang (DerivedCategory Y.Modules))
    (hpc : ∀ y : Y, StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((AlgebraicGeometry.derivedStalkFunctor y).obj T.obj₃))
    (hfib : ∀ (y : Y) (i : ℤ), IsZero (derivedFibreHomology T.obj₃ y i)) :
    IsIso T.mor₁ := by
  refine (Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso
    (O := Y.ringCatSheaf) T.mor₁).2 fun y => ?_
  refine (AlgebraicGeometry.isIso_derivedStalkFunctor_map_iff y T.mor₁).1 ?_
  have hT' := (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).mapDerivedCategory.map_distinguished
    T hT
  exact (Triangle.isZero₃_iff_isIso₁ _ hT').1
    (isZero_of_forall_isZero_residueFibreHomology _ (hpc y) (hfib y))

end Fibrewise

/-! ### The de Rham direct image, the shifted structure sheaf and the fibres -/

section Statement

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `Rf_*Ω^•_{X/Y}` as an object of the unbounded derived category of `𝒪_Y`-modules. -/
abbrev deRhamDirectImage : DerivedCategory Y.Modules :=
  DerivedCategory.Plus.ι.obj (Stacks.DeRhamDirectImage.derivedDeRhamDirectImage f)

/-- The object `𝒪_Y[-m]` of `D(𝒪_Y)`: the structure sheaf in degree zero, shifted by `-m`. -/
abbrev structureSheafShift (Y : Scheme.{u}) (m : ℤ) : DerivedCategory Y.Modules :=
  ((DerivedCategory.singleFunctor Y.Modules 0).obj
    (_root_.SheafOfModules.unit Y.ringCatSheaf))⟦-m⟧

/-- The object `⨁_{i=1}^N 𝒪_Y[-n_i]` of `D(𝒪_Y)`, the source of the Leray--Hirsch morphism. -/
abbrev shiftedStructureSum (Y : Scheme.{u}) {N : ℕ} (n : Fin N → ℕ) :
    DerivedCategory Y.Modules :=
  ⨁ fun i : Fin N => structureSheafShift Y (n i : ℤ)

/-- `H^m_{dR}(X_y/κ(y))`, the de Rham cohomology of the fibre of `f` over a point `y`, in the
abelian-sheaf realization in which the pullback maps of de Rham cohomology are stated. -/
abbrev fibreDeRhamCohomology (y : Y) (m : ℤ) : AddCommGrpCat.{u} :=
  Scheme.Hom.deRhamCohomology (f.fiberToSpecResidueField y) m

/-- `H^m_{dR}(X_y/κ(y))` as a `κ(y)`-module: the module realization of the de Rham cohomology of
the fibre, read over the residue field through the global sections of its spectrum. -/
abbrev fibreDeRhamModule (y : Y) (m : ℤ) : ModuleCat.{u} (Y.residueField y) :=
  (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (Y.residueField y)).inv.hom).obj
    (Scheme.Hom.deRhamCohomologyBaseModule (f.fiberToSpecResidueField y) m)

/-- Restriction of a relative de Rham class to the fibre over `y`: the pullback map of de Rham
cohomology along the cartesian square defining the fibre. -/
abbrev fibreRestriction (y : Y) (m : ℤ) :
    Scheme.Hom.deRhamCohomology f m ⟶ fibreDeRhamCohomology f y m :=
  Scheme.Hom.deRhamCohomologyPullback (f.fiberι y) f (f.fiberToSpecResidueField y)
    (Y.fromSpecResidueField y) pullback.condition m

/-- The inputs to the Leray--Hirsch theorem that the library does not construct: the morphism of
`D(𝒪_Y)` attached to a relative de Rham class, the comparison of the two realizations of the de
Rham cohomology of a fibre, and perfectness of the de Rham direct image. See the implementation
notes of this file for what each of them is and where its missing half lives. -/
structure LerayHirschInput where
  /-- The morphism `𝒪_Y[-m] ⟶ Rf_*Ω^•_{X/Y}` of `D(𝒪_Y)` attached to a class in
  `H^m_{dR}(X/Y)`. -/
  classMorphism (m : ℤ) : ToType (Scheme.Hom.deRhamCohomology f m) →
    (structureSheafShift Y m ⟶ deRhamDirectImage f)
  /-- The comparison of the abelian-sheaf realization of the de Rham cohomology of a fibre with
  its `κ(y)`-module realization. -/
  fibreRealization (y : Y) (m : ℤ) :
    ToType (fibreDeRhamCohomology f y m) →+ ↥(fibreDeRhamModule f y m)
  /-- `Rf_*Ω^•_{X/Y}` is a perfect object of `D(𝒪_Y)`: the perfectness half of
  [Stacks, Tag 0FM0] for the relative de Rham complex. -/
  isPerfect : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
    (deRhamDirectImage f)

variable {f}

/-- A relative de Rham class, restricted to the fibre over `y` and read in the `κ(y)`-module
realization of the de Rham cohomology of that fibre. -/
def LerayHirschInput.fibreClass (D : LerayHirschInput f) (y : Y) (m : ℤ)
    (ξ : ToType (Scheme.Hom.deRhamCohomology f m)) : ↥(fibreDeRhamModule f y m) :=
  D.fibreRealization y m ((fibreRestriction f y m).hom ξ)

/-- **The morphism `⨁_{i=1}^N 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` attached to the classes
`ξ_1, …, ξ_N`**: the direct sum over `i` of the morphisms attached to the individual classes. -/
def classSumMorphism (D : LerayHirschInput f) {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) :
    shiftedStructureSum Y n ⟶ deRhamDirectImage f :=
  biproduct.desc fun i => D.classMorphism (n i : ℤ) (ξ i)

/-- **The fibrewise basis hypothesis**: at every point `y` of `Y` the images of
`ξ_1, …, ξ_N` in the total de Rham cohomology `⨁_m H^m_{dR}(X_y/κ(y))` of the fibre form a basis
over `κ(y)`, the class `ξ_i` contributing in degree `n_i`. -/
def HasFibrewiseBasis (D : LerayHirschInput f) {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) : Prop :=
  ∀ y : Y, ∃ b : Module.Basis (Fin N) (Y.residueField y)
      (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f y m)),
    ∀ i : Fin N, b i = DirectSum.lof (Y.residueField y) ℤ
      (fun m : ℤ => ↥(fibreDeRhamModule f y m)) (n i : ℤ)
      (D.fibreClass y (n i : ℤ) (ξ i))

/-- The remaining geometric input: a cone for the Leray--Hirsch morphism, pseudo-coherence of its
derived stalks, and the base-change identification saying that a fibrewise basis makes the
derived fibres of that cone vanish. -/
structure LerayHirschFibreData (D : LerayHirschInput f) {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) where
  /-- A cone of the morphism attached to the classes. -/
  cone : DerivedCategory Y.Modules
  /-- The morphism from the de Rham direct image to the cone. -/
  mor₂ : deRhamDirectImage f ⟶ cone
  /-- The morphism from the cone to the shifted source. -/
  mor₃ : cone ⟶ (shiftedStructureSum Y n)⟦(1 : ℤ)⟧
  /-- The triangle built from the three morphisms is distinguished, which is what makes `cone` a
  cone of the Leray--Hirsch morphism. -/
  distinguished : Triangle.mk (classSumMorphism D n ξ) mor₂ mor₃ ∈
    distTriang (DerivedCategory Y.Modules)
  /-- The derived stalks of the cone are pseudo-coherent objects of `D(𝒪_{Y,y})`. -/
  stalkPseudoCoherent (y : Y) : StacksDraft.PseudoCoherence.IsPseudoCoherent
    ((AlgebraicGeometry.derivedStalkFunctor y).obj cone)
  /-- The base-change half of [Stacks, Tag 0FM0] for the relative de Rham complex, in the form it
  is used in: a fibrewise basis makes the derived fibres of the cone vanish. -/
  isZero_derivedFibre : HasFibrewiseBasis D n ξ →
    ∀ (y : Y) (i : ℤ), IsZero (derivedFibreHomology cone y i)

/-- **[Stacks, Tag 08CR] for the Leray--Hirsch morphism.** The cone of the morphism attached to
the classes is a perfect object of `D(𝒪_Y)` as soon as its source `⨁_i 𝒪_Y[-n_i]` is, the
perfectness of its target being an input. -/
theorem isPerfect_cone {D : LerayHirschInput f} {N : ℕ} {n : Fin N → ℕ}
    {ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))}
    (C : LerayHirschFibreData D n ξ)
    (hsum : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      (shiftedStructureSum Y n)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) C.cone :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (X := Y.toRingedSpace) _ C.distinguished hsum D.isPerfect

end Statement

end AlgebraicGeometry.DeRhamLerayHirsch

end
