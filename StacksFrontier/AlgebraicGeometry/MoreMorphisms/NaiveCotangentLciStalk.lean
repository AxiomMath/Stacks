module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CartesianSquareStalkLocalization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.NaiveCotangent
public import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkJacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.LciLocalizedInjective

/-!
# The Jacobi-Zariski comparison at a stalk of a local complete intersection morphism

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes with `f` a local complete intersection
morphism, and let `x` be a point of `X`.  The tower of sheaves of commutative rings

`f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`

on `X` of Stacks 0E1Z has at `x` the tower of local rings
`𝒪_{Z,g(f(x))} ⟶ 𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}`, and this file proves that the canonical map of two-term
complexes of `𝒪_{X,x}`-modules

`NL_{(f⁻¹𝒪_Y)_x / (f⁻¹g⁻¹𝒪_Z)_x} ⊗ 𝒪_{X,x} ⟶ NL_{𝒪_{X,x} / (f⁻¹g⁻¹𝒪_Z)_x}`

is **injective on `H₁`**.  This is the stalkwise form of the assertion that puts a zero at the
left of the six-term exact sequence of Stacks 0E44, and it is the only thing missing from
Stacks 0FV3.

The hypothesis is used through affine opens.  Choose affine opens `V ∋ x` of `X`, `U ∋ f(x)` of
`Y` and `W ∋ g(f(x))` of `Z` with `f(V) ⊆ U` and `g(U) ⊆ W`; then `Γ(Y, U) → Γ(X, V)` is a local
complete intersection homomorphism by Stacks 07DB, and the three stalks are localizations of
`Γ(Z, W)`, `Γ(Y, U)` and `Γ(X, V)`.  That is exactly the hypothesis of
`NaiveCotangent.injective_onH₁_nlExtensionBaseChangeMap_of_isLocalization_of_lci`, and the
content of this file is the verification that the three localizations and the seven scalar towers
they sit in are the ones the sheaf-level tower produces at `x`.

## Main results

* `Stacks.NaiveCotangentLciStalk.injective_onH₁_nlExtensionBaseChangeMap_stalk_of_lci`: the
  statement above, for every morphism of extensions inducing the comparison.

## Implementation notes

The three identifications of the stalks with local rings are
`AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso` (for the base `f⁻¹g⁻¹𝒪_Z`, a
double inverse image) and `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` (for the
middle `f⁻¹𝒪_Y`), and the stalk of `𝒪_X` needs none.  The two maps of the tower are carried by
them to the stalk maps of `g` at `f(x)` and of `f` at `x`, by
`AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso_hom_comp_stalkMap` and
`AlgebraicGeometry.BaseChangeStalk.stalk_ringedSpaceStructureMap`; those two statements are what
make the scalar towers over `Γ(Z, W)` hold, through
`Stacks.NaiveCotangentAffineStalk.germ_comp_appLE` — the germ of a restriction of a morphism of
schemes is its stalk map.

The algebra structures are supplied as `letI`s in the statement, as in
`Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalkInverseImage`, because
none of them is found by instance search: the stalks are algebras over one another only through
the stalks of the maps of the tower.  The scalar tower of the tower itself is
`Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget`, which is the one the stalk computation of
the canonical map of Stacks 0E1Z
(`Stacks.NaiveCotangentStalkJacobiZariski.stalkLegNegOneLinear_spaceBaseChangeMap`) carries.

Four of the seven scalar towers over the section rings are not direct: they are assembled from
the others by `Stacks.NaiveCotangentLciStalk.isScalarTower_trans_right` and
`isScalarTower_trans_left`, the two ways of filling in a fourth tower of a square of four rings
given three of them.

## References

* [Stacks Project, Tag 0FV3](https://stacks.math.columbia.edu/tag/0FV3), whose proof this is the
  ring-theoretic input of.
* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4), the injectivity at the
  un-localized level.
* [Stacks Project, Tag 07DB](https://stacks.math.columbia.edu/tag/07DB), a local complete
  intersection morphism on sections over affine opens.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the tower of sheaves of
  rings and its canonical map.
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV) and
  [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H), the stalks of the
  structure sheaf of an affine scheme and of an inverse image.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules
open Stacks.RelativeDifferentialStalk (algebraStalk)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareTarget)
open Stacks.NaiveCotangentAffineStalk

universe u

noncomputable section

namespace Stacks.NaiveCotangentLciStalk

/-! ### Filling in the fourth tower of a square of four rings -/

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra A B] [Algebra B C] [Algebra R B] [Algebra R C] [Algebra A C]

/-- Given a tower `R → A → B`, a tower `A → B → C` and a tower `R → B → C`, the composite
`R → A → C` is a tower. -/
theorem isScalarTower_trans_right [IsScalarTower R A B] [IsScalarTower A B C]
    [IsScalarTower R B C] : IsScalarTower R A C :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R B C, IsScalarTower.algebraMap_eq R A B,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A B C])

/-- Given a tower `R → A → B`, a tower `A → B → C` and a tower `R → A → C`, the composite
`R → B → C` is a tower. -/
theorem isScalarTower_trans_left [IsScalarTower R A B] [IsScalarTower A B C]
    [IsScalarTower R A C] : IsScalarTower R B C :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R A C, IsScalarTower.algebraMap_eq A B C,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R A B])

/-! ### The algebra structure of the sections of `𝒪_Z` on the stalk of `f⁻¹g⁻¹𝒪_Z` -/

section Base

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {W : Z.Opens} {x : X}
  (hgfx : (f ≫ g).base x ∈ W)

/-- `(f⁻¹g⁻¹𝒪_Z)_x` as an algebra over `Γ(Z, W)`: the germ at `g(f(x))` followed by the inverse
of the identification `(f⁻¹g⁻¹𝒪_Z)_x ≅ 𝒪_{Z,g(f(x))}`.  This is the companion of
`Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage` one step further up the tower. -/
abbrev algebraStalkBase :
    Algebra Γ(Z, W)
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x) :=
  ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom.comp
    (Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom).toAlgebra

/-- **`(f⁻¹g⁻¹𝒪_Z)_x = Γ(Z, W)_𝔯`**: for `W` an affine open of `Z` containing `g(f(x))`, the
stalk at `x` of the iterated inverse image of the structure sheaf of `Z` is the localization of
`Γ(Z, W)` at the prime corresponding to `g(f(x))`.  This is Stacks 01HV for `𝒪_Z` transported
along the identification of that stalk with `𝒪_{Z,g(f(x))}`. -/
theorem isLocalization_stalkBase (hW : IsAffineOpen W) :
    letI := algebraStalkBase f g hgfx
    IsLocalization.AtPrime
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      (hW.primeIdealOf ⟨(f ≫ g).base x, hgfx⟩).asIdeal := by
  let := Z.presheaf.algebra_section_stalk (⟨(f ≫ g).base x, hgfx⟩ : W)
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (hW.primeIdealOf ⟨(f ≫ g).base x, hgfx⟩).asIdeal.primeCompl
    (BaseChangeStalk.stalkInverseImageBaseRingIso g f x).symm.commRingCatIsoToRingEquiv).mp
      (hW.isLocalization_stalk ⟨(f ≫ g).base x, hgfx⟩)

/-- **The tower `Γ(Z, W) → (f⁻¹g⁻¹𝒪_Z)_x → (f⁻¹𝒪_Y)_x`.**  The germ at `g(f(x))` of a section of
`𝒪_Z` over `W`, carried into the stalk of `f⁻¹g⁻¹𝒪_Z` and then along the first map of the tower,
is its restriction to `U` followed by the germ at `f(x)` carried into the stalk of `f⁻¹𝒪_Y`.

Under the two identifications of the stalks with `𝒪_{Z,g(f(x))}` and `𝒪_{Y,f(x)}` the first map
of the tower is the stalk map of `g` at `f(x)`
(`AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso_hom_comp_stalkMap`), and the
germ of a restriction of `g` is that stalk map
(`Stacks.NaiveCotangentAffineStalk.germ_comp_appLE`). -/
theorem isScalarTower_stalkBase {U : Y.Opens} (hUW : U ≤ g ⁻¹ᵁ W) (hfx : f.base x ∈ U) :
    letI := algebraAppLE g hUW
    letI := algebraStalkBase f g hgfx
    letI := algebraStalkInverseImage f hfx
    letI : Algebra Γ(Z, W)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
      ((algebraMap Γ(Y, U)
          ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)).comp
        (algebraMap Γ(Z, W) Γ(Y, U))).toAlgebra
    letI : Algebra
        ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
      algebraStalk (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom x
    IsScalarTower Γ(Z, W)
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) := by
  let := algebraAppLE g hUW
  let := algebraStalkBase f g hgfx
  let := algebraStalkInverseImage f hfx
  let _ : Algebra Γ(Z, W)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    ((algebraMap Γ(Y, U)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)).comp
      (algebraMap Γ(Z, W) Γ(Y, U))).toAlgebra
  let _ : Algebra
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    algebraStalk (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom x
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
  -- both sides, written out on an element
  show ((Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv.hom
      ((Y.presheaf.germ U (f.base x) hfx).hom ((g.appLE W U hUW).hom r))) =
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom).hom
      ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom
        ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))
  rw [show ((Y.presheaf.germ U (f.base x) hfx).hom ((g.appLE W U hUW).hom r)) =
      (g.stalkMap (f.base x)).hom ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r) from
    RingHom.congr_fun (germ_comp_appLE g hUW hfx hgfx) r]
  have happ := CommRingCat.hom_ext_iff.mp
    (BaseChangeStalk.stalkInverseImageBaseRingIso_hom_comp_stalkMap g f x)
  have h2 := RingHom.congr_fun happ
    ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom
      ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))
  change (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom.hom
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom).hom
        ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom
          ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))) =
    (g.stalkMap (f.base x)).hom
      ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).hom.hom
        ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom
          ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))) at h2
  rw [show ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).hom.hom
        ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom
          ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))) =
      ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r) from
    congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom
        ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))
      (BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv_hom_id] at h2
  rw [← h2]
  exact congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom).hom
        ((BaseChangeStalk.stalkInverseImageBaseRingIso g f x).inv.hom
          ((Z.presheaf.germ W ((f ≫ g).base x) hgfx).hom r))))
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom_inv_id

end Base

/-! ### The main statement -/

section Main

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The Jacobi-Zariski comparison at a stalk of a local complete intersection morphism is
injective on `H₁`.**  For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` with `f` a local
complete intersection morphism, and `x` a point of `X`, the canonical map of two-term complexes
of `𝒪_{X,x}`-modules

`NL_{(f⁻¹𝒪_Y)_x / (f⁻¹g⁻¹𝒪_Z)_x} ⊗ 𝒪_{X,x} ⟶ NL_{𝒪_{X,x} / (f⁻¹g⁻¹𝒪_Z)_x}`

attached to the stalk at `x` of the tower `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of Stacks 0E1Z is
injective on `H₁`.

The statement holds for every morphism of extensions inducing the comparison, any two being
homotopic; the one the stalk of the canonical map of Stacks 0E1Z produces is
`Stacks.NaiveCotangentTowerStalk.stalkTowerHomBase`. -/
theorem injective_onH₁_nlExtensionBaseChangeMap_stalk_of_lci
    (hf : IsLocalCompleteIntersectionMorphism f) (x : X) :
    letI : Algebra
        ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
      algebraStalk (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom x
    letI : Algebra
        ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
        ↑(X.presheaf.stalk x) :=
      algebraStalk ((inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom) ≫
        ringedSpaceStructureMap f.toLRSHom.toShHom).hom x
    letI := algebraStalkInverseImageStructureMap f (x := x)
    haveI : IsScalarTower
        ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
        ↑(X.presheaf.stalk x) :=
      stalkIsScalarTowerSquareTarget
        (inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom)
        (inverseImageMiddleRing f.toLRSHom.toShHom) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
        ((inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom) ≫
          ringedSpaceStructureMap f.toLRSHom.toShHom)
        (ringedSpaceStructureMap f.toLRSHom.toShHom) x rfl
    ∀ h : (Algebra.Generators.self
          ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
          ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
            Y.sheaf).presheaf.stalk x)).toExtension.Hom
        (Algebra.Generators.self
          ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
          ↑(X.presheaf.stalk x)).toExtension,
      Function.Injective (NaiveCotangent.nlExtensionBaseChangeMap
        (T := ↑(X.presheaf.stalk x)) h).onH₁ := by
  -- the three affine opens
  obtain ⟨W, hgfxW, -⟩ :=
    AlgebraicGeometry.exists_affineOpen_mem_le (g.base (f.base x)) ⊤ (Opens.mem_top _)
  obtain ⟨U, hfxU, hUW⟩ :=
    AlgebraicGeometry.exists_affineOpen_mem_le (f.base x) (g ⁻¹ᵁ W.1) hgfxW
  obtain ⟨V, hxV, hVU⟩ := AlgebraicGeometry.exists_affineOpen_mem_le x (f ⁻¹ᵁ U.1) hfxU
  have hVW : V.1 ≤ (f ≫ g) ⁻¹ᵁ W.1 := fun z hz => hUW (hVU hz)
  have hgfx : (f ≫ g).base x ∈ W.1 := hgfxW
  -- the algebra structures of the section rings
  let _ : Algebra Γ(Z, W.1) Γ(Y, U.1) := algebraAppLE g hUW
  let _ : Algebra Γ(Y, U.1) Γ(X, V.1) := algebraAppLE f hVU
  let _ : Algebra Γ(Z, W.1) Γ(X, V.1) := algebraAppLE (f ≫ g) hVW
  have htowerSections : IsScalarTower Γ(Z, W.1) Γ(Y, U.1) Γ(X, V.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show ((f ≫ g).appLE W.1 V.1 hVW).hom =
        (f.appLE U.1 V.1 hVU).hom.comp (g.appLE W.1 U.1 hUW).hom
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom
        (Scheme.Hom.appLE_comp_appLE f g W.1 U.1 V.1 hUW hVU).symm)
  -- the algebra structures of the stalks over the section rings
  let _ : Algebra Γ(Z, W.1)
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x) :=
    algebraStalkBase f g hgfx
  let _ : Algebra Γ(Y, U.1)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    algebraStalkInverseImage f hfxU
  let _ : Algebra Γ(X, V.1) ↑(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V.1)
  let _ : Algebra Γ(Y, U.1) ↑(X.presheaf.stalk x) := algebraStalkOfAppLE f hVU hxV
  let _ : Algebra Γ(Z, W.1) ↑(X.presheaf.stalk x) := algebraStalkOfAppLE (f ≫ g) hVW hxV
  let _ : Algebra Γ(Z, W.1)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    ((algebraMap Γ(Y, U.1)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)).comp
      (algebraMap Γ(Z, W.1) Γ(Y, U.1))).toAlgebra
  -- the algebra structures of the stalks over one another
  let _ : Algebra
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    algebraStalk (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom x
  let _ : Algebra
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(X.presheaf.stalk x) :=
    algebraStalk ((inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom) ≫
      ringedSpaceStructureMap f.toLRSHom.toShHom).hom x
  let _ := algebraStalkInverseImageStructureMap f (x := x)
  have htowerStalks : IsScalarTower
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      ↑(X.presheaf.stalk x) :=
    stalkIsScalarTowerSquareTarget
      (inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom)
      (inverseImageMiddleRing f.toLRSHom.toShHom) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
      ((inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom) ≫
        ringedSpaceStructureMap f.toLRSHom.toShHom)
      (ringedSpaceStructureMap f.toLRSHom.toShHom) x rfl
  -- the towers through the section rings
  have h₁ : IsScalarTower Γ(Y, U.1) Γ(X, V.1) ↑(X.presheaf.stalk x) :=
    isScalarTower_appLE f hVU hxV
  have h₂ : IsScalarTower Γ(Z, W.1) Γ(X, V.1) ↑(X.presheaf.stalk x) :=
    isScalarTower_appLE (f ≫ g) hVW hxV
  have h₃ : IsScalarTower Γ(Y, U.1)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      ↑(X.presheaf.stalk x) := isScalarTower_stalkInverseImage f hVU hxV hfxU
  have h₄ : IsScalarTower Γ(Z, W.1) Γ(Y, U.1) ↑(X.presheaf.stalk x) :=
    isScalarTower_trans_right (A := Γ(Y, U.1)) (B := Γ(X, V.1))
  have h₅ : IsScalarTower Γ(Z, W.1) Γ(Y, U.1)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h₆ : IsScalarTower Γ(Z, W.1)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
      ↑(X.presheaf.stalk x) :=
    isScalarTower_trans_left (A := Γ(Y, U.1))
      (B := ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x))
  have h₇ : IsScalarTower Γ(Z, W.1)
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x) :=
    isScalarTower_stalkBase f g hgfx hUW hfxU
  have h₈ : IsScalarTower Γ(Z, W.1)
      ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x)
      ↑(X.presheaf.stalk x) :=
    isScalarTower_trans_right
      (A := ↑((inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom).presheaf.stalk x))
      (B := ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x))
  -- the three localizations
  have hlocA := isLocalization_stalkBase f g hgfx W.2
  have hlocB := isLocalization_stalkInverseImage f hfxU U.2
  have hlocC := isLocalization_stalk hxV V.2
  -- the local complete intersection condition on the section rings
  have hlci : RingHom.IsLocalCompleteIntersection (algebraMap Γ(Y, U.1) Γ(X, V.1)) :=
    AlgebraicGeometry.NaiveCotangentLocalCompleteIntersection.isLocalCompleteIntersection_appLE
      f hf U.2 V.2 hVU
  exact fun h =>
    NaiveCotangent.injective_onH₁_nlExtensionBaseChangeMap_of_isLocalization_of_lci hlci
      (W.2.primeIdealOf ⟨(f ≫ g).base x, hgfx⟩).asIdeal.primeCompl
      (U.2.primeIdealOf ⟨f.base x, hfxU⟩).asIdeal.primeCompl
      (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl h

end Main

end Stacks.NaiveCotangentLciStalk

end

end
