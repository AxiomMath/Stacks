module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Cotangent.AtiyahClassSmallSiteFirstVertex
public import StacksFrontier.Cotangent.AtiyahClassBigSiteResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The first vertex of the Atiyah triangle at the site `C_{B/A}` itself

The first term of the Atiyah triangle of [Stacks, Tag 09DD] is `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 M̲)`, and the
source displays it as `L_{B/A} ⊗^𝐋_B M`. This file carries out, at the site `C_{B/A}` of
[Stacks, Tag 08PR] itself -- read on its `CategoryTheory.AsSmall` model
`CommAlgCat.atiyahSite`, on which the triangle is formed -- the two steps of that identification
which are formal:

* the vertex is stripped of the sheafification and of the corepresenting-object spelling of its
  tensor factor, which needs [Stacks, Tag 04BL] for this site;
* the resulting objectwise tensor product is recognised as the `𝒪`-module underlying a
  `B̲`-module, by the projection formula.

Both are the arguments used at the small model of the footnote-restricted site, run here at
`C_{B/A}` itself. They cannot be transported from that model: the restriction to a full
subcategory of bounded-cardinality augmentations changes both `Mod(B̲)` and `Lπ_!`, and the
inclusion of the small model into `C_{B/A}` is only fully faithful
(`CommAlgCat.fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite`), the unrestricted site not
being essentially small at all.

The universe lifts are forced: the morphism of topoi `π` of [Stacks, Tag 08PF] is formed at a
coefficient universe containing the objects of the site, so `𝒪` has sections `ULift P`, `A̲` has
value `ULift A`, `B̲` has value `ULift B`, and the sections of `Ω_{𝒪/A}` are
`Ω[ULift P ⁄ ULift A]`. That is exactly how
`CommAlgCat.polynomialRelativeDifferentials` reads them on `CommAlgCat.polynomialSite`, and
`KaehlerDifferential.uliftLinearEquiv` is the comparison with `Ω[P⁄A]`.

## Main definitions

* `CommAlgCat.atiyahRelativeDifferentialsPresheaf` and
  `CommAlgCat.atiyahRelativeDifferentials`: the sheaf `Ω_{𝒪/A}` of `𝒪`-modules on
  `CommAlgCat.atiyahSite`, with `CommAlgCat.atiyahUniversalDerivation` its universal derivation.
* `CommAlgCat.atiyahConstantSheaf` and `CommAlgCat.atiyahAugmentationComm`: the constant sheaf of
  *commutative* rings `B̲` and the augmentation `𝒪 ⟶ B̲` at that spelling, whose forgetful image
  is `CommAlgCat.atiyahCoefficientHom` on the nose.
* `CommAlgCat.atiyahModuleOverConstant`: a `B`-module read as a presheaf of modules over `B̲`.

## Main results

* `CommAlgCat.atiyahRelativeDifferentialsCorepresentableBy`: **[Stacks, Tag 04BL] for
  `CommAlgCat.atiyahSite`** -- `Ω_{𝒪/A}` corepresents the relative derivations of `𝒪` over `A̲`,
  so it is the sheaf of differentials the principal-parts sequence is built from, and
  `CommAlgCat.atiyahDerivationsCoreprXIso` identifies the corepresenting object the Atiyah
  triangle is written with.
* `CommAlgCat.atiyahFirstVertexTensorIso`: the first vertex before `Lπ_!`, with the
  sheafification and the corepresenting-object spelling undone.
* `CommAlgCat.atiyahFirstVertexRestrictionIso`: **`M̲ ⊗_𝒪 Ω_{𝒪/A}` is the `𝒪`-module underlying
  the `B̲`-module `M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`**, which is the projection formula
  `Stacks.FlatChangeOfRings.baseChangeNatIso` at the constant `B̲`-module `M`.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleSheaves)

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The sheaf of relative differentials on `CommAlgCat.atiyahSite` -/

/-- The presheaf of relative differentials of `A̲ ⟶ 𝒪` on `CommAlgCat.atiyahSite`, whose value
over `(P, α)` is the module of Kähler differentials of the universe lift of `A → P`. -/
def atiyahRelativeDifferentialsPresheaf :
    PresheafOfModules.{u + 1} (atiyahRingSheaf A B).obj :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (atiyahBaseHom A B).hom

/-- **The sheaf of relative differentials `Ω_{𝒪/A}` on `CommAlgCat.atiyahSite`**, a sheaf of
`𝒪`-modules. It is the objectwise module of Kähler differentials, which is already a sheaf
because the topology is chaotic. -/
def atiyahRelativeDifferentials :
    moduleSheaves.{u + 1, u + 1, u + 1, u + 1} (atiyahStructureSheaf A B) where
  val := atiyahRelativeDifferentialsPresheaf A B
  isSheaf := Presheaf.isSheaf_bot _

/-- The universal relative derivation of `𝒪` over `A̲` with values in `Ω_{𝒪/A}`. -/
def atiyahUniversalDerivation :
    (atiyahRelativeDifferentials A B).val.Derivation' (atiyahBaseHom A B).hom :=
  PresheafOfModules.DifferentialsConstruction.derivation' (atiyahBaseHom A B).hom

/-- **[Stacks, Tag 04BL] for `CommAlgCat.atiyahSite`.** `Ω_{𝒪/A}` corepresents the functor
sending a sheaf of `𝒪`-modules to the relative derivations of `𝒪` over `A̲` with values in it, so
it is the sheaf of differentials of `A̲ ⟶ 𝒪` in the sense the principal-parts sequence uses. Only
the presheaf-level universal property of Mathlib's `relativeDifferentials'` is needed: every
presheaf on a chaotic site is a sheaf, so a morphism of sheaves of modules is a morphism of the
underlying presheaves. -/
def atiyahRelativeDifferentialsCorepresentableBy :
    (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u + 1} (atiyahBaseSheaf A B)
        (atiyahStructureSheaf A B)
        (atiyahBaseHom A B)).CorepresentableBy
      (atiyahRelativeDifferentials A B) := by
  refine AlgebraicGeometry.SheafOfModules.universalDerivationCorepresentableBy.{u + 1, u + 1,
    u + 1, u + 1} _ _ _ (atiyahUniversalDerivation A B) (fun F D => ?_)
  refine ⟨⟨(PresheafOfModules.DifferentialsConstruction.isUniversal'
    (atiyahBaseHom A B).hom).desc D⟩, ?_, fun g hg => ?_⟩
  · exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (atiyahBaseHom A B).hom).fac D
  · exact SheafOfModules.hom_ext
      ((PresheafOfModules.DifferentialsConstruction.isUniversal'
        (atiyahBaseHom A B).hom).postcomp_injective _ _
          (hg.trans ((PresheafOfModules.DifferentialsConstruction.isUniversal'
            (atiyahBaseHom A B).hom).fac D).symm))

/-- **The first vertex of the Atiyah triangle is formed with `Ω_{𝒪/A}`.** The corepresenting
object that the sequence of first principal parts is built from is identified with the objectwise
sheaf of Kähler differentials of `CommAlgCat.atiyahSite`, by uniqueness of corepresenting
objects. -/
def atiyahDerivationsCoreprXIso :
    (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u + 1} (atiyahBaseSheaf A B)
        (atiyahStructureSheaf A B) (atiyahBaseHom A B)).coreprX ≅
      atiyahRelativeDifferentials A B :=
  haveI := (atiyahRelativeDifferentialsCorepresentableBy A B).isCorepresentable
  ((atiyahRelativeDifferentialsCorepresentableBy A B).isoCoreprX).symm

/-! ### The augmentation at commutative-ring coefficients -/

/-- The constant sheaf of **commutative** rings `B̲` on `CommAlgCat.atiyahSite`. The coefficient
map of derived lower shriek is a map of presheaves of rings; the projection formula
`Stacks.FlatChangeOfRings.baseChangeNatIso` needs it at the commutative spelling. -/
abbrev atiyahConstantSheaf :
    Sheaf (⊥ : GrothendieckTopology (atiyahSite A B)) CommRingCat.{u + 1} :=
  ⟨(Functor.const (atiyahSite A B)ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (B : Type u))), Presheaf.isSheaf_bot _⟩

/-- **The augmentation `𝒪 ⟶ B̲` as a map of sheaves of commutative rings.** Forgetting the
commutativity returns `CommAlgCat.atiyahCoefficientHom`, on the nose. -/
def atiyahAugmentationComm : atiyahStructureSheaf A B ⟶ atiyahConstantSheaf A B :=
  ⟨Functor.whiskerLeft (atiyahSiteFunctor A B) (polynomialAugmentationPresheaf A B)⟩

/-- Forgetting the commutativity of `CommAlgCat.atiyahAugmentationComm` is
`CommAlgCat.atiyahCoefficientHom`: both are the augmentations of the objects of the site, read
through the universe lift. -/
theorem atiyahAugmentationComm_forget :
    Functor.whiskerRight (atiyahAugmentationComm A B).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      atiyahCoefficientHom A B :=
  rfl

/-- A `B`-module read as a presheaf of modules over the constant presheaf of rings `B̲`. -/
abbrev atiyahModuleOverConstant (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :
    PresheafOfModules.{u + 1} ((Functor.const (atiyahSite A B)ᵒᵖ).obj
      (RingCat.of (ULift.{u + 1} (B : Type u)))) :=
  (Stacks.ChaoticSite.constantModulePresheafEquivalence
    (ULift.{u + 1} (B : Type u))).inverse.obj ((Functor.const _).obj M)

/-! ### The first vertex before `Lπ_!` -/

variable (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- **The first vertex of the Atiyah triangle before `Lπ_!`, with the sheafification and the
corepresenting-object spelling undone.** The sheafification is invertible because the topology is
chaotic (`Stacks.ChaoticSite.sheafificationValIso`), and the corepresenting object is identified
with `Ω_{𝒪/A}` by `CommAlgCat.atiyahDerivationsCoreprXIso`. -/
def atiyahFirstVertexTensorIso :
    Stacks.Atiyah.chaoticModel.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (atiyahStructureSheaf A B)).flip.obj
          (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u + 1} (atiyahBaseSheaf A B)
            (atiyahStructureSheaf A B)
            (atiyahBaseHom A B)).coreprX).obj (atiyahModuleSheaf A B M)) ≅
      (Stacks.tensorRight (O := (atiyahStructureSheaf A B).obj)
            (atiyahRelativeDifferentialsPresheaf A B)).obj
        ((PresheafOfModules.restrictScalars (atiyahCoefficientHom A B)).obj
          (atiyahModuleOverConstant A B M)) :=
  Stacks.ChaoticSite.sheafificationValIso _ _ ≪≫
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObjIsoRight _
      (Stacks.Atiyah.chaoticModel.mapIso (atiyahDerivationsCoreprXIso A B))

/-- **`M̲ ⊗_𝒪 Ω_{𝒪/A}` is the `𝒪`-module underlying a `B̲`-module.** The `B̲`-module is
`M ⊗_{B̲} (B̲ ⊗_𝒪 Ω_{𝒪/A})`, with sections `M ⊗_{ULift B} (ULift B ⊗_{ULift P} Ω[ULift P ⁄
ULift A])`, and the identification is the projection formula
`Stacks.FlatChangeOfRings.baseChangeNatIso`, sectionwise
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
def atiyahFirstVertexRestrictionIso :
    (Stacks.tensorRight (O := (atiyahStructureSheaf A B).obj)
          (atiyahRelativeDifferentialsPresheaf A B)).obj
        ((PresheafOfModules.restrictScalars (atiyahCoefficientHom A B)).obj
          (atiyahModuleOverConstant A B M)) ≅
      (PresheafOfModules.restrictScalars (atiyahCoefficientHom A B)).obj
        ((Stacks.tensorRight (O := (atiyahConstantSheaf A B).obj)
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
            (atiyahAugmentationComm A B).hom).obj
              (atiyahRelativeDifferentialsPresheaf A B))).obj
          (atiyahModuleOverConstant A B M)) :=
  ((Stacks.FlatChangeOfRings.baseChangeNatIso (atiyahAugmentationComm A B)
    (atiyahRelativeDifferentialsPresheaf A B)).app (atiyahModuleOverConstant A B M)).symm

end CommAlgCat

end
