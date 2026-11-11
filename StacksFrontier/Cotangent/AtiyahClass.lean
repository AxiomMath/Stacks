module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSequenceStructure
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah class of a module

Let `A → B` be a ring map, let `M` be a `B`-module and let `𝒪` be the structure sheaf of the
site `C_{B/A}` of polynomial `A`-algebras augmented to `B`. The sheaves of first principal parts
relative to the constant sheaf `A` sit in a short exact sequence of `𝒪`-modules

`0 ⟶ Ω_{𝒪/A} ⊗_𝒪 M ⟶ P¹_{𝒪/A}(M) ⟶ M ⟶ 0`,

and applying the exact functor `Lπ_! : D(𝒪) ⟶ D(B)` to it gives a distinguished triangle

`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M) ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ Lπ_!(M) ⟶ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M)[1]`

in `D(B)`. Its last arrow is the *Atiyah class* of `M`.

## Main definitions

* `Stacks.Atiyah.principalPartsShortComplex`: the sequence of first principal parts of a sheaf of
  modules on a chaotic site, as a short complex.
* `Stacks.Atiyah.triangle`: its image under derived lower shriek with coefficients.
* `Stacks.Atiyah.atiyahClass`: the last arrow of that triangle.
* `CommAlgCat.atiyahSite`: a small model of the site `C_{B/A}`, with its structure sheaf
  `CommAlgCat.atiyahStructureSheaf`, the constant sheaf of rings `A`
  `CommAlgCat.atiyahBaseSheaf`, the map `CommAlgCat.atiyahBaseHom` between them, and the
  coefficient map `CommAlgCat.atiyahCoefficientHom` to the constant sheaf `B`.
* `CommAlgCat.atiyahModuleSheaf`: a `B`-module read as a sheaf of `𝒪`-modules on `C_{B/A}`
  through the augmentations.
* `CommAlgCat.polynomialAtiyahTriangle` and `CommAlgCat.polynomialAtiyahClass`: the triangle and
  the Atiyah class of a module over the ring map `A → B`.
* `CommAlgCat.polynomialAtiyahClassOfIso`: the Atiyah class of a module in the form displayed by
  the source, `M ⟶ L_{B/A} ⊗_B^𝐋 M[1]`, read through identifications of the first and third
  terms of the triangle with `L_{B/A} ⊗_B^𝐋 M` and `M`.

## Main results

* `Stacks.Atiyah.principalPartsShortComplex_shortExact`: the sequence of principal parts is short
  exact, and `Stacks.Atiyah.presheafShortComplex_shortExact` is the same read on presheaves of
  modules, which is where derived lower shriek is defined.
* `Stacks.Atiyah.triangle_distinguished` and
  `CommAlgCat.polynomialAtiyahTriangle_distinguished`: the triangle is distinguished.
* `Stacks.Atiyah.triangle_obj₁`, `Stacks.Atiyah.triangle_obj₂`, `Stacks.Atiyah.triangle_obj₃` and
  `CommAlgCat.polynomialAtiyahTriangle_obj₂`: the three terms of the triangle are `Lπ_!` of the
  relative differentials tensored with the module, of its sheaf of first principal parts, and of
  the module itself.
* `CommAlgCat.polynomialAtiyahTriangle_distinguished_of_iso`: the triangle written with its first
  and third terms replaced by objects identified with them, which is the displayed form of the
  source, and `CommAlgCat.polynomialAtiyahClassOfIso_mem_distinguished`, the same triangle with
  its last arrow named as the Atiyah class.

## Implementation notes

The site `C_{B/A}` has its objects in `Type (u + 1)` and its morphisms in `Type u`, while derived
lower shriek with coefficients is available for a small category; `CommAlgCat.atiyahSite` is
therefore the `AsSmall` model of `C_{B/A}`, over which the structure sheaf and the augmentation
are read by restriction along the comparison functor. No topology is transported: the topology of
`C_{B/A}` is chaotic, so the model carries the topology `⊥` and every presheaf on it is a sheaf.

The sequence of principal parts is produced for sheaves of modules and derived lower shriek
consumes presheaves of modules; on a chaotic site these are the same thing, and the comparison
used is `Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence`.

The derived categories are the standard model, which is the one derived lower shriek with
coefficients is constructed over; the local instance is given a priority because the imports
also supply a second model of the derived category of presheaves of modules.

The identifications `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M) = L_{B/A} ⊗^L_B M` (Tag 08PT and the flatness of the
terms of `L_{B/A}`) and `Lπ_!(M) = M` (Tag 08QE) name the first and third terms of the displayed
triangle in the source. This file reads the triangle with its endpoints left as `Lπ_!` of the two
sheaves; `CommAlgCat.polynomialAtiyahTriangle_distinguished_of_iso` and
`CommAlgCat.polynomialAtiyahClassOfIso` take arbitrary identifications of the endpoints as
arguments. Both identifications are proved downstream, at the site `C_{B/A}` itself:
`StacksFrontier/Cotangent/AtiyahClassBigSiteEndpoints.lean` for the third term and
`StacksFrontier/Cotangent/AtiyahClassBigSiteCanonical.lean` for the first, where the Atiyah class
`M ⟶ (L_{B/A} ⊗_B^𝐋 M)[1]` of Tag 09DE is defined as `CommAlgCat.atiyahClass`.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD) and
  [Tag 09DE](https://stacks.math.columbia.edu/tag/09DE), the Atiyah class.
* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts, and [Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ), derived lower
  shriek with coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.SheafOfModules
  (moduleSheaves PrincipalPartsSequence principalPartsSequenceOfSite)

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.Atiyah

/-! ### The triangle of principal parts on a chaotic site -/

variable {C : Type u} [SmallCategory C]
  {O₁ O₂ : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}} {φ : O₁ ⟶ O₂}
  (S : PrincipalPartsSequence.{u, u, u, u} O₁ O₂ φ) (F : moduleSheaves.{u, u, u, u} O₂)

/-- The inclusion `Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F)` followed by the projection
`P¹_{O₂/O₁}(F) ⟶ F` vanishes. -/
theorem inclusion_comp_projection : S.inclusion.app F ≫ S.projection.app F = 0 :=
  (S.shortExact F).elim fun h _ => h

/-- The sequence `Ω_{O₂/O₁} ⊗_{O₂} F ⟶ P¹_{O₂/O₁}(F) ⟶ F` of first principal parts of `F`, as a
short complex of sheaves of modules. -/
def principalPartsShortComplex : ShortComplex (moduleSheaves.{u, u, u, u} O₂) :=
  ShortComplex.mk _ _ (inclusion_comp_projection S F)

/-- The sequence of first principal parts is short exact. -/
theorem principalPartsShortComplex_shortExact :
    (principalPartsShortComplex S F).ShortExact :=
  (S.shortExact F).elim fun _ h => h

/-- On a chaotic site, sheaves of `O₂`-modules are presheaves of modules over the underlying
presheaf of rings of `O₂`. -/
abbrev chaoticModel : moduleSheaves.{u, u, u, u} O₂ ⥤
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O₂).obj :=
  (Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O₂)).functor

/-- The sequence of first principal parts of `F`, read as a short complex of presheaves of
modules. -/
def presheafShortComplex : ShortComplex
    (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O₂).obj) :=
  (principalPartsShortComplex S F).map chaoticModel

/-- The sequence of first principal parts is short exact as a sequence of presheaves of
modules. -/
theorem presheafShortComplex_shortExact : (presheafShortComplex S F).ShortExact := by
  have h := principalPartsShortComplex_shortExact S F
  have := h.mono_f
  have := h.epi_g
  exact h.map chaoticModel

variable (B : Type u) [Ring B]
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O₂).obj ⟶
    (Functor.const Cᵒᵖ).obj (RingCat.of B))

/-- Derived lower shriek `Lπ_! : D(O₂) ⟶ D(B)` with coefficients in the map `ψ : O₂ ⟶ B̲`. -/
abbrev lowerShriek := Stacks.ChaoticSite.derivedColimitWithCoefficients B
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O₂).obj ψ

/-- The image under `Lπ_!` of the triangle attached to the sequence of first principal parts of
`F`: a triangle `Lπ_!(Ω ⊗ F) ⟶ Lπ_!(P¹(F)) ⟶ Lπ_!(F) ⟶ Lπ_!(Ω ⊗ F)[1]` in `D(B)`. -/
def triangle : Triangle (DerivedCategory (ModuleCat.{u} B)) :=
  (lowerShriek B ψ).mapTriangle.obj (presheafShortComplex_shortExact S F).singleTriangle

/-- The triangle of first principal parts is distinguished: it is the image of a short exact
sequence under an exact functor of triangulated categories. -/
theorem triangle_distinguished : triangle S F B ψ ∈ distinguishedTriangles :=
  (lowerShriek B ψ).map_distinguished _
    (presheafShortComplex_shortExact S F).singleTriangle_distinguished

/-- The first term of the triangle is `Lπ_!` of the relative differentials tensored with `F`. -/
theorem triangle_obj₁ : (triangle S F B ψ).obj₁ =
    (lowerShriek B ψ).obj ((DerivedCategory.singleFunctor _ 0).obj
      (chaoticModel.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O₂).flip.obj
          (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u} O₁ O₂ φ).coreprX).obj F))) :=
  rfl

/-- The second term of the triangle is `Lπ_!` of the sheaf of first principal parts of `F`. -/
theorem triangle_obj₂ : (triangle S F B ψ).obj₂ =
    (lowerShriek B ψ).obj ((DerivedCategory.singleFunctor _ 0).obj
      (chaoticModel.obj (S.principalParts.obj F))) :=
  rfl

/-- The third term of the triangle is `Lπ_!` of `F`. -/
theorem triangle_obj₃ : (triangle S F B ψ).obj₃ =
    (lowerShriek B ψ).obj ((DerivedCategory.singleFunctor _ 0).obj (chaoticModel.obj F)) :=
  rfl

/-- The Atiyah class of `F`: the last arrow `Lπ_!(F) ⟶ Lπ_!(Ω ⊗ F)[1]` of the triangle of first
principal parts. -/
def atiyahClass : (triangle S F B ψ).obj₃ ⟶ (triangle S F B ψ).obj₁⟦(1 : ℤ)⟧ :=
  (triangle S F B ψ).mor₃

/-- The triangle of first principal parts, written with its first and third terms replaced by
objects identified with them. -/
theorem triangle_distinguished_of_iso (L N : DerivedCategory (ModuleCat.{u} B))
    (e₁ : (triangle S F B ψ).obj₁ ≅ L) (e₃ : (triangle S F B ψ).obj₃ ≅ N) :
    Triangle.mk (e₁.inv ≫ (triangle S F B ψ).mor₁) ((triangle S F B ψ).mor₂ ≫ e₃.hom)
        (e₃.inv ≫ (triangle S F B ψ).mor₃ ≫
          (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (1 : ℤ)).map e₁.hom) ∈
      distinguishedTriangles :=
  isomorphic_distinguished _ (triangle_distinguished S F B ψ) _
    (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp) (by simp))

end Stacks.Atiyah

namespace CommAlgCat

/-! ### The site `C_{B/A}` and its sheaves of rings -/

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- A small model of the site `C_{B/A}`, whose objects live in `Type (u + 1)` and whose morphisms
live in `Type u`. -/
abbrev atiyahSite := AsSmall.{u} (polynomialSite A B)

/-- The comparison functor from presheaves on `C_{B/A}` to presheaves on its small model. -/
abbrev atiyahSiteFunctor : (atiyahSite A B)ᵒᵖ ⥤ (polynomialSite A B)ᵒᵖ :=
  (AsSmall.equiv (C := polynomialSite A B)).inverse.op

/-- The structure sheaf `𝒪` of `C_{B/A}`, read on the small model. The topology is chaotic, so
every presheaf is a sheaf. -/
def atiyahStructureSheaf :
    Sheaf (⊥ : GrothendieckTopology (atiyahSite A B)) CommRingCat.{u + 1} :=
  ⟨atiyahSiteFunctor A B ⋙ polynomialStructurePresheaf A B, Presheaf.isSheaf_bot _⟩

/-- The constant sheaf of rings `A` on `C_{B/A}`, over which the relative differentials and the
principal parts of `𝒪` are taken. -/
def atiyahBaseSheaf :
    Sheaf (⊥ : GrothendieckTopology (atiyahSite A B)) CommRingCat.{u + 1} :=
  ⟨(Functor.const (atiyahSite A B)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)),
    Presheaf.isSheaf_bot _⟩

/-- The map of sheaves of rings `A ⟶ 𝒪` given by the `A`-algebra structure of each object of
`C_{B/A}`. -/
def atiyahBaseHom : atiyahBaseSheaf A B ⟶ atiyahStructureSheaf A B :=
  ⟨{ app X := CommRingCat.ofHom
        ((ULift.ringEquiv (R := (((atiyahSiteFunctor A B).obj X).unop.unop.obj.left :
            Type u))).symm.toRingHom.comp
          ((algebraMap A _).comp (ULift.ringEquiv (R := A)).toRingHom))
     naturality X Y f := by
       apply CommRingCat.hom_ext
       ext a
       exact congrArg ULift.up
         ((((atiyahSiteFunctor A B).map f).unop.unop.hom.left.hom.commutes a.down).symm) }⟩

/-- The sheaf of rings underlying `𝒪`. -/
abbrev atiyahRingSheaf : Sheaf (⊥ : GrothendieckTopology (atiyahSite A B)) RingCat.{u + 1} :=
  Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (atiyahStructureSheaf A B)

/-- The map `𝒪 ⟶ B̲` given by the augmentations, as the coefficient map of derived lower
shriek. -/
def atiyahCoefficientHom :
    (atiyahRingSheaf A B).obj ⟶
      (Functor.const (atiyahSite A B)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} (B : Type u))) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (atiyahSiteFunctor A B) (polynomialAugmentationPresheaf A B))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-! ### The Atiyah triangle of a module -/

variable (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- A `B`-module read as a sheaf of `𝒪`-modules on `C_{B/A}`: the constant sheaf with value `M`,
with `P` acting through the augmentation `α : P → B`. -/
def atiyahModuleSheaf : moduleSheaves.{u + 1, u + 1, u + 1, u + 1} (atiyahStructureSheaf A B) :=
  (Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence.{u + 1}
      (atiyahRingSheaf A B)).inverse.obj
    ((Stacks.ChaoticSite.coefficientRestriction (ULift.{u + 1} (B : Type u))
      (atiyahRingSheaf A B).obj (atiyahCoefficientHom A B)).obj ((Functor.const _).obj M))

/-- The sequence of first principal parts of the sheaves of `𝒪`-modules on `C_{B/A}`, relative to
the constant sheaf of rings `A`. -/
def atiyahPrincipalPartsSequence :
    PrincipalPartsSequence.{u + 1, u + 1, u + 1, u + 1} (atiyahBaseSheaf A B)
      (atiyahStructureSheaf A B) (atiyahBaseHom A B) :=
  principalPartsSequenceOfSite.{u + 1, u + 1, u + 1, u + 1} _ _ (atiyahBaseHom A B)

/-- **Stacks 09DD.** The Atiyah triangle of a `B`-module `M`: the image under
`Lπ_! : D(𝒪) ⟶ D(B)` of the sequence of first principal parts of `M` on `C_{B/A}`. -/
@[stacks 09DD "the triangle"]
def polynomialAtiyahTriangle :
    Triangle (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))) :=
  Stacks.Atiyah.triangle (atiyahPrincipalPartsSequence A B) (atiyahModuleSheaf A B M)
    (ULift.{u + 1} (B : Type u)) (atiyahCoefficientHom A B)

/-- **Stacks 09DD.** The Atiyah triangle is distinguished. -/
@[stacks 09DD "the triangle is distinguished"]
theorem polynomialAtiyahTriangle_distinguished :
    polynomialAtiyahTriangle A B M ∈ distinguishedTriangles :=
  Stacks.Atiyah.triangle_distinguished _ _ _ _

/-- The second term of the Atiyah triangle is `Lπ_!` of the sheaf of first principal parts of
`M` on `C_{B/A}`. -/
theorem polynomialAtiyahTriangle_obj₂ : (polynomialAtiyahTriangle A B M).obj₂ =
    (Stacks.Atiyah.lowerShriek (ULift.{u + 1} (B : Type u)) (atiyahCoefficientHom A B)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.Atiyah.chaoticModel.obj
        ((atiyahPrincipalPartsSequence A B).principalParts.obj (atiyahModuleSheaf A B M)))) :=
  rfl

/-- **Stacks 09DD.** The Atiyah class of `M`: the last arrow of the Atiyah triangle. -/
@[stacks 09DD "the Atiyah class, the last arrow of the triangle"]
def polynomialAtiyahClass :
    (polynomialAtiyahTriangle A B M).obj₃ ⟶ (polynomialAtiyahTriangle A B M).obj₁⟦(1 : ℤ)⟧ :=
  (polynomialAtiyahTriangle A B M).mor₃

/-- **Stacks 09DD.** The Atiyah triangle written with its first and third terms replaced by
objects identified with them: for `L` identified with `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M)` and `N` identified
with `Lπ_!(M)`, the sequence `L ⟶ Lπ_!(P¹_{𝒪/A}(M)) ⟶ N ⟶ L[1]` is a distinguished triangle,
whose last arrow is the Atiyah class of `M`. -/
@[stacks 09DD "the displayed triangle"]
theorem polynomialAtiyahTriangle_distinguished_of_iso
    (L N : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
    (e₁ : (polynomialAtiyahTriangle A B M).obj₁ ≅ L)
    (e₃ : (polynomialAtiyahTriangle A B M).obj₃ ≅ N) :
    Triangle.mk (e₁.inv ≫ (polynomialAtiyahTriangle A B M).mor₁)
        ((polynomialAtiyahTriangle A B M).mor₂ ≫ e₃.hom)
        (e₃.inv ≫ (polynomialAtiyahTriangle A B M).mor₃ ≫
          (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
            (1 : ℤ)).map e₁.hom) ∈
      distinguishedTriangles :=
  Stacks.Atiyah.triangle_distinguished_of_iso _ _ _ _ L N e₁ e₃

/-- The Atiyah class of `M` read through identifications of the endpoints of the triangle: for
`L` identified with `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M)` and `N` identified with `Lπ_!(M)` this is the last arrow
`N ⟶ L[1]` of the distinguished triangle of Tag 09DD. At the canonical identifications
`L = L_{B/A} ⊗_B^𝐋 M` and `N = M` it is the Atiyah class `M ⟶ L_{B/A} ⊗_B^𝐋 M[1]` of Tag 09DE,
which is `CommAlgCat.atiyahClass` (`StacksFrontier/Cotangent/AtiyahClassBigSiteCanonical.lean`).
That it is the last arrow of the displayed triangle is
`CommAlgCat.polynomialAtiyahClassOfIso_mem_distinguished`. -/
def polynomialAtiyahClassOfIso
    (L N : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
    (e₁ : (polynomialAtiyahTriangle A B M).obj₁ ≅ L)
    (e₃ : (polynomialAtiyahTriangle A B M).obj₃ ≅ N) : N ⟶ L⟦(1 : ℤ)⟧ :=
  e₃.inv ≫ polynomialAtiyahClass A B M ≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
      (1 : ℤ)).map e₁.hom

/-- The Atiyah class of `M` is the last arrow of the displayed distinguished triangle of
Tag 09DD. -/
theorem polynomialAtiyahClassOfIso_mem_distinguished
    (L N : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))))
    (e₁ : (polynomialAtiyahTriangle A B M).obj₁ ≅ L)
    (e₃ : (polynomialAtiyahTriangle A B M).obj₃ ≅ N) :
    Triangle.mk (e₁.inv ≫ (polynomialAtiyahTriangle A B M).mor₁)
        ((polynomialAtiyahTriangle A B M).mor₂ ≫ e₃.hom)
        (polynomialAtiyahClassOfIso A B M L N e₁ e₃) ∈ distinguishedTriangles :=
  polynomialAtiyahTriangle_distinguished_of_iso A B M L N e₁ e₃

end CommAlgCat

end
