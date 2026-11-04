module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafScheme
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a scheme over a ring

Let `Λ` be a ring and let `X` be a scheme over `Λ`, with structure morphism
`p : X ⟶ Spec Λ`. The cotangent complex `L_{X/Spec Λ}` is the cotangent complex of the
homomorphism `p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` of sheaves of rings on the small Zariski site of `X`, and
the constant sheaf `Λ̲` with value `Λ` maps canonically to `p⁻¹𝒪_{Spec Λ}`. The resulting tower
`Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` has `L_{𝒪_X/Λ̲}` and `L_{X/Spec Λ}` as the second and third vertices
of its fundamental triangle, and the canonical arrow between them is the comparison of
Tag 08V6.

## Main definitions

* `AlgebraicGeometry.SchemeOverRing.structureRingedSpaceHom` is the structure morphism read as a
  morphism of ringed spaces, and `AlgebraicGeometry.SchemeOverRing.pullbackStructureSheaf`,
  `AlgebraicGeometry.SchemeOverRing.pullbackStructureMap` are `p⁻¹𝒪_{Spec Λ}` and `p^♯` typed on
  the site of open subsets of `X`, where `AlgebraicGeometry.SchemeOverRing.structureSheafOfSite`
  is `𝒪_X`.
* `AlgebraicGeometry.SchemeOverRing.constantBaseSheaf` is the constant sheaf `Λ̲` of rings with
  value `Λ` on `X`, and `AlgebraicGeometry.SchemeOverRing.constantToPullback` is its canonical
  homomorphism to `p⁻¹𝒪_{Spec Λ}`, named through
  `AlgebraicGeometry.SchemeOverRing.constantAdjunction` by
  `AlgebraicGeometry.SchemeOverRing.pullbackUnitTop`; the composite with `p^♯` is
  `AlgebraicGeometry.SchemeOverRing.constantStructureMap` and
  `AlgebraicGeometry.SchemeOverRing.globalStructureMap` is the induced `Λ`-algebra structure of
  the global sections of `X`.
* `AlgebraicGeometry.SchemeOverRing.cotangentComplexConstant` is `L_{𝒪_X/Λ̲}` and
  `AlgebraicGeometry.SchemeOverRing.cotangentComplexRelative` is `L_{X/Spec Λ}`, both complexes
  of sheaves of `𝒪_X`-modules on the small Zariski site of `X`.
* `AlgebraicGeometry.SchemeOverRing.constantComparison` is the canonical comparison
  `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}`.
* `AlgebraicGeometry.SchemeOverRing.pullbackCotangentComplex` is the first vertex
  `L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗_{p⁻¹𝒪_{Spec Λ}} 𝒪_X` of the fundamental triangle of the tower, the
  pullback of the complex the source calls `L_q`.

## Main results

* `AlgebraicGeometry.SchemeOverRing.constantStructureMap_eq`: the composite
  `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` is the `Λ`-algebra structure of `𝒪_X` determined by the ring map
  `Λ ≅ Γ(Spec Λ, 𝒪) ⟶ Γ(X, 𝒪_X)` on global sections, so the left-hand side of Tag 08V6 is
  formed over the structure `p` itself induces.
* `AlgebraicGeometry.SchemeOverRing.cotangentComplexRelative_eq`: the right-hand side is the
  cotangent complex of `p` as a morphism of ringed spaces, Tag 08UU.
* `AlgebraicGeometry.SchemeOverRing.isIso_constantComparison_iff`: granted the short exact
  sequence Tag 08SZ carries for this tower, the comparison is an isomorphism in `D(𝒪_X)` exactly
  when the first vertex of the fundamental triangle vanishes there.

## Implementation notes

The constant sheaf is Mathlib's `CategoryTheory.constantSheaf`, the sheafification of the
constant presheaf; sheafification of commutative rings on the site of opens of a space in the
universe of its sections is found by instance search. A homomorphism out of it is named by a ring
map out of `Λ` into global sections, through `CategoryTheory.constantSheafAdj` at the terminal
open `⊤`, so `constantToPullback` needs no choice: the ring map it is named by is
`Λ ≅ Γ(Spec Λ, 𝒪) ⟶ Γ(X, p⁻¹𝒪_{Spec Λ})`, the unit of the inverse-image adjunction read on the
whole space.

The site is `Opens X` with its topology of open covers, whose objects and morphisms both lie in
the universe `u` of the sections of `𝒪_X`, so the three universes of
`CategoryTheory.Sheaf.cotangentComplex` all specialize to `u` here. The structure morphism enters
as a morphism of ringed spaces, which is the form in which the source defines `L_{X/Y}`
(Tag 08T2 through Tag 08UU) and the form the library's Tag 08T4 takes.

## References

* [Stacks Project, Tag 08V6](https://stacks.math.columbia.edu/tag/08V6)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ), the fundamental triangle
  of a tower of sheaves of rings.
* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU), the cotangent complex of
  a morphism of ringed spaces.
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0) and
  [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), the two inputs of the
  vanishing the source proves and this module does not.
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap
  inverseImageSheaf inverseImageStructureMap homEquiv_inverseImageStructureMap)

universe u t

namespace AlgebraicGeometry.SchemeOverRing

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of Λ))

/-- The structure morphism of a scheme over `Λ`, read as a morphism of ringed spaces. -/
abbrev structureRingedSpaceHom : X.toRingedSpace ⟶ (Spec (CommRingCat.of Λ)).toRingedSpace :=
  Stacks.Smooth.ringedSpaceHom p

/-- `𝒪_X`, typed as a sheaf of commutative rings on the site of open subsets of `X` rather than
as a sheaf on the space `X`. The two types are definitionally equal; only in this one is the
site, and with it every universe, written out. -/
def structureSheafOfSite (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} :=
  X.sheaf

/-- The constant sheaf `Λ̲` of commutative rings with value `Λ` on the small Zariski site of a
scheme `X`: the sheafification of the constant presheaf. -/
def constantBaseSheaf (Λ : Type u) [CommRing Λ] (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}).obj (CommRingCat.of Λ)

/-- `p⁻¹𝒪_{Spec Λ}`, the inverse image of the structure sheaf of the base, typed as a sheaf of
commutative rings on the site of open subsets of `X`. -/
def pullbackStructureSheaf : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} :=
  inverseImageSheaf (structureRingedSpaceHom Λ p)

/-- `p^♯ : p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`, the inverse-image form of the structure map of `p`, typed on
the site of open subsets of `X`. -/
def pullbackStructureMap : pullbackStructureSheaf Λ p ⟶ structureSheafOfSite X :=
  inverseImageStructureMap (structureRingedSpaceHom Λ p)

/-- The ring map `Λ ≅ Γ(Spec Λ, 𝒪) ⟶ Γ(X, p⁻¹𝒪_{Spec Λ})` given by the unit of the
inverse-image adjunction read on the whole space. -/
def pullbackUnitTop : CommRingCat.of Λ ⟶ (pullbackStructureSheaf Λ p).obj.obj (op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
    ((sheafAdjunction (structureRingedSpaceHom Λ p)).unit.app
      (Spec (CommRingCat.of Λ)).toRingedSpace.sheaf).hom.app (op ⊤)

/-- The constant-sheaf adjunction on the small Zariski site of `X`, at the terminal open. -/
def constantAdjunction (X : Scheme.{u}) :
    constantSheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} ⊣
      (sheafSections (Opens.grothendieckTopology ↥X) CommRingCat.{u}).obj (op ⊤) :=
  constantSheafAdj (Opens.grothendieckTopology ↥X) CommRingCat.{u}
    (T := (⊤ : Opens ↥X)) isTerminalTop

/-- The canonical homomorphism `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ}`: the one named by `pullbackUnitTop` under
the constant-sheaf adjunction at the terminal open. -/
def constantToPullback : constantBaseSheaf Λ X ⟶ pullbackStructureSheaf Λ p :=
  ((constantAdjunction X).homEquiv (CommRingCat.of Λ) (pullbackStructureSheaf Λ p)).symm
    (pullbackUnitTop Λ p)

/-- The `Λ`-algebra structure `Λ̲ ⟶ 𝒪_X` of the structure sheaf: the canonical map to
`p⁻¹𝒪_{Spec Λ}` followed by `p^♯`. -/
def constantStructureMap : constantBaseSheaf Λ X ⟶ structureSheafOfSite X :=
  constantToPullback Λ p ≫ pullbackStructureMap Λ p

/-- The `Λ`-algebra structure `Λ ≅ Γ(Spec Λ, 𝒪) ⟶ Γ(X, 𝒪_X)` on global sections determined by
the structure morphism. -/
def globalStructureMap : CommRingCat.of Λ ⟶ (structureSheafOfSite X).obj.obj (op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ p.appTop

/-- The `Λ`-algebra structure of `constantStructureMap` is the one named by the ring map
`Λ ≅ Γ(Spec Λ, 𝒪) ⟶ Γ(X, 𝒪_X)` on global sections, so it is the structure `p` itself
induces. -/
theorem constantStructureMap_eq :
    constantStructureMap Λ p =
      ((constantAdjunction X).homEquiv (CommRingCat.of Λ) (structureSheafOfSite X)).symm
        (globalStructureMap Λ p) := by
  have key := homEquiv_inverseImageStructureMap (structureRingedSpaceHom Λ p)
  rw [Adjunction.homEquiv_unit] at key
  have hsec : ((sheafAdjunction (structureRingedSpaceHom Λ p)).unit.app
        (Spec (CommRingCat.of Λ)).toRingedSpace.sheaf).hom.app (op ⊤) ≫
      (pullbackStructureMap Λ p).hom.app (op ⊤) = p.appTop := by
    have h2 : ((sheafAdjunction (structureRingedSpaceHom Λ p)).unit.app
          (Spec (CommRingCat.of Λ)).toRingedSpace.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (structureRingedSpaceHom Λ p).hom.base).map
          (inverseImageStructureMap (structureRingedSpaceHom Λ p))).hom.app (op ⊤) =
        (structureSheafMap (structureRingedSpaceHom Λ p)).hom.app (op ⊤) := by rw [key]
    exact h2
  have hring : pullbackUnitTop Λ p ≫
      ((sheafSections (Opens.grothendieckTopology ↥X) CommRingCat.{u}).obj (op ⊤)).map
        (pullbackStructureMap Λ p) = globalStructureMap Λ p :=
    (Category.assoc _ _ _).trans
      (congrArg (CategoryStruct.comp (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv) hsec)
  exact ((constantAdjunction X).homEquiv_naturality_right_symm (pullbackUnitTop Λ p)
      (pullbackStructureMap Λ p)).symm.trans
    (congrArg
      (((constantAdjunction X).homEquiv (CommRingCat.of Λ) (structureSheafOfSite X)).symm)
      hring)

/-- `L_{𝒪_X/Λ̲}`, the cotangent complex of the `Λ`-algebra structure of `𝒪_X` over the constant
sheaf. -/
abbrev cotangentComplexConstant :
    CochainComplex
      (CategoryTheory.Sheaf.targetModules.{u, u, u} (Opens.grothendieckTopology ↥X)
        (structureSheafOfSite X)) ℤ :=
  CategoryTheory.Sheaf.cotangentComplex.{u, u, u} (Opens.grothendieckTopology ↥X)
    (constantStructureMap Λ p)

/-- `L_{X/Spec Λ}`, the cotangent complex of the structure morphism. -/
abbrev cotangentComplexRelative :
    CochainComplex
      (CategoryTheory.Sheaf.targetModules.{u, u, u} (Opens.grothendieckTopology ↥X)
        (structureSheafOfSite X)) ℤ :=
  CategoryTheory.Sheaf.cotangentComplex.{u, u, u} (Opens.grothendieckTopology ↥X)
    (pullbackStructureMap Λ p)

/-- `L_{X/Spec Λ}` is the cotangent complex of the structure morphism as a morphism of ringed
spaces, the complex of Tag 08UU. -/
theorem cotangentComplexRelative_eq :
    cotangentComplexRelative Λ p =
      Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex (structureRingedSpaceHom Λ p) :=
  rfl

/-- The first vertex `L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗_{p⁻¹𝒪_{Spec Λ}} 𝒪_X` of the fundamental triangle of
the tower `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`, with the degreewise tensor product: the pullback to `X` of
the complex the source calls `L_q`. -/
abbrev pullbackCotangentComplex :
    CochainComplex
      (CategoryTheory.Sheaf.targetModules.{u, u, u} (Opens.grothendieckTopology ↥X)
        (structureSheafOfSite X)) ℤ :=
  CategoryTheory.Sheaf.baseChangedCotangentComplex.{u, u, u} (Opens.grothendieckTopology ↥X)
    (constantToPullback Λ p) (pullbackStructureMap Λ p)

/-- The canonical comparison `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}`: the change-of-base-ring map of the tower
`Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`. -/
@[stacks 08V6 "the canonical comparison L_{O_X/const Lambda} ⟶ L_{X/Spec Lambda} of the tag, \
  constructed unconditionally as the change-of-base arrow of Tag 08SZ for the tower \
  const Lambda ⟶ p^-1 O_{Spec Lambda} ⟶ O_X, with the constant sheaf being Mathlib's \
  constantSheaf and the target the cotangent complex of p of Tag 08UU \
  (cotangentComplexRelative_eq). That it is an ISOMORPHISM is NOT claimed by this declaration; \
  see isIso_constantComparison_iff and the module documentation"]
def constantComparison : cotangentComplexConstant Λ p ⟶ cotangentComplexRelative Λ p :=
  CategoryTheory.Sheaf.towerCotangentChangeOfBase.{u, u, u} (Opens.grothendieckTopology ↥X)
    (constantToPullback Λ p) (pullbackStructureMap Λ p)

/-- Granted the short exact sequence Tag 08SZ carries for the tower `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`, the
canonical comparison `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}` is an isomorphism in `D(𝒪_X)` exactly when the
first vertex `L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗_{p⁻¹𝒪_{Spec Λ}} 𝒪_X` of the fundamental triangle vanishes
there.

The hypothesis carried is the one Tag 08SZ carries, in the same shape: a short complex `S` of
complexes of sheaves of `𝒪_X`-modules that is short exact (`hS`), whose three terms are the three
vertices (`e₁`, `e₂`, `e₃`) and whose two maps are the two canonical arrows (`hf`, `hg`). -/
@[stacks 08V6 "the REDUCTION of the tag, not the tag: an IFF between the comparison being an \
  isomorphism in D(O_X) and the vanishing of the first vertex of the fundamental triangle, the \
  pullback of the source's L_q. The vanishing -- the source's Tag 08T0 plus Tag 08R2 step -- is \
  NOT proved here and is not assumed either; it is the right-hand side. ONE carried hypothesis, \
  exactly the one Tag 08SZ carries: the short exact sequence `S`/`hS` realizing the two \
  canonical arrows (`hf`, `hg`) on the three vertices (`e1`, `e2`, `e3`), the sheaf-level \
  analogue of Tag 08SD, absent from this library. See the module documentation"]
theorem isIso_constantComparison_iff
    [HasDerivedCategory.{t} (CategoryTheory.Sheaf.targetModules.{u, u, u}
      (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))]
    (S : ShortComplex (CochainComplex
      (CategoryTheory.Sheaf.targetModules.{u, u, u} (Opens.grothendieckTopology ↥X)
        (structureSheafOfSite X)) ℤ))
    (hS : S.ShortExact) (e₁ : S.X₁ ≅ pullbackCotangentComplex Λ p)
    (e₂ : S.X₂ ≅ cotangentComplexConstant Λ p)
    (e₃ : S.X₃ ≅ cotangentComplexRelative Λ p)
    (hf : S.f = e₁.hom ≫ CategoryTheory.Sheaf.towerCotangentBaseChange.{u, u, u}
      (Opens.grothendieckTopology ↥X) (constantToPullback Λ p)
      (pullbackStructureMap Λ p) ≫ e₂.inv)
    (hg : S.g = e₂.hom ≫ constantComparison Λ p ≫ e₃.inv) :
    IsIso ((DerivedCategory.Q (C := CategoryTheory.Sheaf.targetModules.{u, u, u}
          (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))).map
        (constantComparison Λ p)) ↔
      IsZero ((DerivedCategory.Q (C := CategoryTheory.Sheaf.targetModules.{u, u, u}
        (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))).obj
          (pullbackCotangentComplex Λ p)) := by
  obtain ⟨δ, hδ⟩ :=
    CategoryTheory.Sheaf.exists_distTriang_cotangentComplexDerived_of_shortExact.{u, u, u, t}
      (Opens.grothendieckTopology ↥X) (constantToPullback Λ p)
      (pullbackStructureMap Λ p) S hS e₁ e₂ e₃ hf hg
  exact (Triangle.isZero₁_iff_isIso₂ _ hδ).symm

end AlgebraicGeometry.SchemeOverRing

end
