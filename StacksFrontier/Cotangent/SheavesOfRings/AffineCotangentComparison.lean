module

public import StacksFrontier.Cotangent.SchemeCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsCotangentComparison
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.FromSpecImageTop

/-!
# The cotangent complex of a morphism of schemes over an affine open

Let `f : X ⟶ Y` be a morphism of schemes, let `U ⊂ X` be an affine open with `B = 𝒪_X(U)`, and
let `V ⊂ Y` be an open with `f(U) ⊂ V` and `A = 𝒪_Y(V)`. This file constructs the canonical map

```
  ~(L_{B/A}) ⟶ L_{X/Y}|_U
```

of complexes of `𝒪_U`-modules, where `~` is the associated-sheaf functor of Schemes, Lemma
01I7 on `Spec B` and `U` is identified with `Spec B` through `IsAffineOpen.fromSpec`.

The construction follows the proof of Tag 08T3. Remark 08SX supplies a canonical map of
complexes of `B`-modules

```
  L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)} ⟶ L_{X/Y}(U),
```

the canonical ring map `A ⟶ (f⁻¹𝒪_Y)(U)` — built here from the unit of the inverse
image/direct image adjunction for sheaves of commutative rings — turns this into a map
`L_{B/A} ⟶ L_{X/Y}(U)` by functoriality of the cotangent complex of a ring map in a
commutative square of rings, and the universal property of `~` (Tag 01I7, available as the
tilde–`Γ` adjunction) converts a map of complexes of `B`-modules `L_{B/A} ⟶ Γ(L_{X/Y}|_U)` into
a map of complexes of `𝒪_U`-modules out of `~(L_{B/A})`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.zariskiInverseImageStructureSheaf` is `f⁻¹𝒪_Y` on the small Zariski
  site of `X`, and `AlgebraicGeometry.Scheme.Hom.inverseImageUnit` is the unit of the inverse
  image/direct image adjunction at `𝒪_Y`, read through the identification of the direct image
  with restriction along the inverse image of opens.
* `AlgebraicGeometry.Scheme.Hom.inverseImageSections` is the canonical ring map
  `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` attached to an inclusion `U ≤ f⁻¹V`.
* `AlgebraicGeometry.Scheme.Hom.affineAlgebra` is `𝒪_X(U)` as an `𝒪_Y(V)`-algebra, and
  `AlgebraicGeometry.Scheme.Hom.affineAlgebraSquare` is the commutative square of ring maps
  `𝒪_Y(V) → (f⁻¹𝒪_Y)(U)`, `𝒪_X(U) = 𝒪_X(U)` it fits into.
* `AlgebraicGeometry.Scheme.Hom.affineSections` compares sections over an affine open `U` with
  the global sections of the restriction to `Spec 𝒪_X(U)`.
* `AlgebraicGeometry.Scheme.Hom.cotangentSectionsComparison` is the resulting map of complexes
  of `𝒪_X(U)`-modules `L_{B/A} ⟶ L_{X/Y}(U)`, and
  `AlgebraicGeometry.Scheme.Hom.gammaCotangentComparison` is the same map read as a map into
  the global sections of `L_{X/Y}|_U`.
* `AlgebraicGeometry.Scheme.Hom.affineCotangentComparison` is the canonical map
  `~(L_{B/A}) ⟶ L_{X/Y}|_U`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.inverseImageUnit_comp`: the unit followed by the direct image
  of the inverse-image form of `f♯` is `f♯` itself.
* `AlgebraicGeometry.Scheme.Hom.inverseImageSections_comp`: the canonical ring map
  `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` followed by `(f⁻¹𝒪_Y)(U) ⟶ 𝒪_X(U)` is `f.appLE V U`, so the two
  algebra structures on `𝒪_X(U)` are compatible and the square of rings commutes.
* `AlgebraicGeometry.Scheme.Hom.map_eqToHom_fromSpec_image_top`: the ring map by which
  `𝒪_X(U)` acts on the global sections over `Spec 𝒪_X(U)` of a restriction is restriction along
  `fromSpec ''ᵁ ⊤ = U`.

## Implementation notes

The open `V` need not be affine: the construction uses only `f(U) ⊂ V`, so the map is built for
an arbitrary open `V` containing the image of `U`.

That this map is an isomorphism in `D(𝒪_U)`, checked on stalks (Tag 08TL) using the localization
property of the cotangent complex (Tag 08SF), and that it is compatible with restriction to smaller
affine opens are proved in `StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentComparisonIsIso`.

The two topologies and the restriction functor are written with
`TopologicalSpace.Opens.grothendieckTopology ↥X` rather than with `X.zariskiRingedTopos.J`:
the `Functor.IsContinuous` instance for the inverse image of opens is stated for the former,
and instance search does not see through the structure projection.

`AlgebraicGeometry.Scheme.Hom.sectionsOver` and
`AlgebraicGeometry.Scheme.Hom.globalSectionsRestrict` respell
`CategoryTheory.Sheaf.moduleSections` and the composite with `moduleSpecΓFunctor` as functors
into `ModuleCat Γ(X, U)`. The respelling is what makes the two `Γ(X, U)`-module structures
visible to instance search: the sections functor of Remark 08SX lands in modules over
`CategoryTheory.Sheaf.sectionsAlgebra`, which is `Γ(X, U)` definitionally but not at the
transparency instance search uses. Both `abbrev`s are reducible for that reason.

The identity restriction of scalars along the square's `𝒪_X(U) = 𝒪_X(U)` is not stripped by
`ModuleCat.restrictScalarsId'`: the module structure `Module.compHom _ (RingHom.id _)` is
definitionally the original one, so the target of
`CommAlgCat.squareCotangentComplexMap` for this square is already the complex of sections and
no comparison isomorphism intervenes.

The two cotangent complexes are instantiated at the universe triple `u, u, u`: the site of
opens of a scheme of universe `u` has its objects and its morphisms in `Type u` and `𝒪_X`
takes values in `CommRingCat.{u}`, which pins the third universe of
`CategoryTheory.Sheaf.cotangentComplex` to `u` as well.

## References

* [Stacks Project, Tag 08T3](https://stacks.math.columbia.edu/tag/08T3)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08SF](https://stacks.math.columbia.edu/tag/08SF)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` -/

/-- Restriction of sheaves of commutative rings along the inverse image of opens: the direct
image of sheaves of sets along the morphism of topoi induced by `f` is restriction along
`TopologicalSpace.Opens.map f.base`, and this is the same functor for sheaves of commutative
rings. -/
abbrev zariskiRestriction :
    Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u} :=
  (Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)

/-- `f⁻¹𝒪_Y`, the inverse image of the structure sheaf of `Y` as a sheaf of commutative rings
on the small Zariski site of `X`; the cotangent complex of `f` is `L_{X/Y} = L_{𝒪_X/f⁻¹𝒪_Y}`. -/
abbrev zariskiInverseImageStructureSheaf : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u} :=
  (inverseImageCommRingFunctor f.zariskiRingedToposHom.toToposHom).obj Y.zariskiRingedTopos.O

/-- The comparison of the inverse image along restriction with restriction itself, taken at
`𝒪_X`. This is the isomorphism that the structure map of `f` as a morphism of ringed topoi is
defined through. -/
abbrev structureRestrictionIso :=
  restrictionCommRingIso (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)
    (Opens.map f.base) X.sheaf

/-- The unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y` of the inverse image/direct image adjunction for sheaves of
commutative rings, read through the identification of the direct image with restriction along
the inverse image of opens. Its sections over `V` are a ring map
`𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(f⁻¹V)`. -/
def inverseImageUnit : Y.sheaf ⟶ (zariskiRestriction f).obj (zariskiInverseImageStructureSheaf f) :=
  (commRingImageAdjunction f.zariskiRingedToposHom.toToposHom).unit.app
      Y.zariskiRingedTopos.O ≫
    (restrictionCommRingIso (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)
      (Opens.map f.base) (zariskiInverseImageStructureSheaf f)).hom

/-- The structure map of `f` as a morphism of ringed topoi is the unit followed by the direct
image of its inverse-image form: this is the triangle identity of the adjunction, written out
for the adjunct. -/
theorem fSharp_eq :
    f.zariskiRingedToposHom.fSharp =
      (commRingImageAdjunction f.zariskiRingedToposHom.toToposHom).unit.app
          Y.zariskiRingedTopos.O ≫
        (pushforwardCommRingFunctor f.zariskiRingedToposHom.toToposHom).map
          (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) :=
  (Equiv.apply_symm_apply
      ((commRingImageAdjunction f.zariskiRingedToposHom.toToposHom).homEquiv
        Y.zariskiRingedTopos.O X.zariskiRingedTopos.O)
      f.zariskiRingedToposHom.fSharp).symm.trans
    (Adjunction.homEquiv_unit _ _ _ _)

/-- The unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y`, followed by the restriction along the inverse image of opens of
the inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map, is the structure map `f♯` of `f`
itself. -/
theorem inverseImageUnit_comp :
    inverseImageUnit f ≫ (zariskiRestriction f).map
        (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) =
      zariskiSharp f :=
  (Category.assoc _ _ _).trans
    ((congrArg
        (fun z => (commRingImageAdjunction f.zariskiRingedToposHom.toToposHom).unit.app
          Y.zariskiRingedTopos.O ≫ z)
        (restrictionCommRingIso_naturality (Opens.grothendieckTopology ↥Y)
            (Opens.grothendieckTopology ↥X) (Opens.map f.base)
            (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom)).symm).trans
      (((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ (structureRestrictionIso f).hom) (fSharp_eq f).symm)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => zariskiSharp f ≫ z)
            (Iso.inv_hom_id (structureRestrictionIso f))).trans (Category.comp_id _)))))

/-- The canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` attached to an inclusion `U ≤ f⁻¹V`: the
unit of the adjunction over `V`, followed by restriction from `f⁻¹V` to `U`. -/
def inverseImageSections {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    Γ(Y, V) ⟶ (zariskiInverseImageStructureSheaf f).obj.obj (op U) :=
  (inverseImageUnit f).hom.app (op V) ≫
    (zariskiInverseImageStructureSheaf f).obj.map (homOfLE e).op

/-- On sections over `V`, the unit followed by the inverse-image form of the structure map is
the map `f.app V : 𝒪_Y(V) ⟶ 𝒪_X(f⁻¹V)`. -/
theorem inverseImageUnit_app_comp (V : Y.Opens) :
    (inverseImageUnit f).hom.app (op V) ≫
        (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom).hom.app
          (op (f ⁻¹ᵁ V)) = f.app V :=
  congrArg (fun k : Y.sheaf ⟶ (zariskiRestriction f).obj X.sheaf => k.hom.app (op V))
    (inverseImageUnit_comp f)

/-- The canonical ring map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)`, followed by the structure map
`(f⁻¹𝒪_Y)(U) ⟶ 𝒪_X(U)`, is `f.appLE V U`. So the `𝒪_Y(V)`-algebra structure on `𝒪_X(U)` given
by `f` factors through the `(f⁻¹𝒪_Y)(U)`-algebra structure. -/
theorem inverseImageSections_comp {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    inverseImageSections f e ≫
        (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom).hom.app (op U) =
      f.appLE V U e :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (inverseImageUnit f).hom.app (op V) ≫ z)
        ((RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom).hom.naturality
          (homOfLE e).op)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ X.presheaf.map (homOfLE e).op)
          (inverseImageUnit_app_comp f V))))

/-! ### The square of rings and the comparison on sections -/

section Square

variable {U : X.Opens} {V : Y.Opens}

/-- The sections `𝒪_X(U)`, read as an algebra over `𝒪_Y(V)` along `f`: this is the `B` over `A`
of Tag 08T3. -/
abbrev affineAlgebra (e : U ≤ f ⁻¹ᵁ V) : CommAlgCat.{u} Γ(Y, V) :=
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  CommAlgCat.of Γ(Y, V) Γ(X, U)

/-- The sections `𝒪_X(U)`, read as an algebra over `(f⁻¹𝒪_Y)(U)`: the algebra of sections of
Remark 08SX for the homomorphism `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
abbrev inverseImageSectionsAlgebra (U : X.Opens) :
    CommAlgCat.{u} ((zariskiInverseImageStructureSheaf f).obj.obj (op U)) :=
  CategoryTheory.Sheaf.sectionsAlgebra (Opens.grothendieckTopology ↥X)
    (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) (op U)

/-- The commutative square of ring maps whose base map is the canonical
`𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` and whose top map is the identity of `𝒪_X(U)`. It commutes by
`AlgebraicGeometry.Scheme.Hom.inverseImageSections_comp`. -/
def affineAlgebraSquare (e : U ≤ f ⁻¹ᵁ V) :
    CommAlgCat.AlgebraSquare.{u, u, u} Γ(Y, V)
        ((zariskiInverseImageStructureSheaf f).obj.obj (op U))
        (affineAlgebra f e) (inverseImageSectionsAlgebra f U) where
  base := (inverseImageSections f e).hom
  map := RingHom.id Γ(X, U)
  map_algebraMap a :=
    (congrArg (fun k : Γ(Y, V) ⟶ Γ(X, U) => k.hom a) (inverseImageSections_comp f e)).symm

end Square

/-! ### Sections over an affine open as global sections on its spectrum -/

section AffineOpen

variable {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)

/-- The ring map by which `𝒪_X(U)` acts on the global sections over `Spec 𝒪_X(U)` of a
restriction along `IsAffineOpen.fromSpec` is restriction along `fromSpec ''ᵁ ⊤ = U`. -/
theorem map_eqToHom_fromSpec_image_top :
    X.presheaf.map (eqToHom (hU.fromSpec_image_top)).op =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
        (Spec Γ(X, U)).presheaf.map (Opens.leTop ⊤).op ≫
          (hU.fromSpec.appIso ⊤).inv := by
  rw [← Iso.cancel_iso_hom_right _ _ (hU.fromSpec.appIso ⊤)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE,
    hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  congr 1

/-- Sections over `U` of a sheaf of `𝒪_X`-modules, as a module over `𝒪_X(U)`: the sections
functor of Remark 08SX, with its target respelled so that the ring is `Γ(X, U)` reducibly. -/
abbrev sectionsOver (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  CategoryTheory.Sheaf.moduleSections (Opens.grothendieckTopology ↥X)
    (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) (op U)

/-- Global sections over `Spec 𝒪_X(U)` of the restriction along `IsAffineOpen.fromSpec`, as a
module over `𝒪_X(U)`. -/
abbrev globalSectionsRestrict (hU : IsAffineOpen U) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  Scheme.Modules.restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor

/-- Sections over an affine open `U` compared with the global sections over `Spec 𝒪_X(U)` of the
restriction: restriction along `fromSpec ''ᵁ ⊤ = U`, which is `𝒪_X(U)`-linear by
`AlgebraicGeometry.Scheme.Hom.map_eqToHom_fromSpec_image_top`. -/
def affineSectionsApp (M : X.Modules) :
    (sectionsOver f U).obj M ⟶ (globalSectionsRestrict hU).obj M :=
  ModuleCat.ofHom (R := Γ(X, U))
      (X := (sectionsOver f U).obj M) (Y := (globalSectionsRestrict hU).obj M)
    { toFun := fun x => M.presheaf.map (eqToHom (hU.fromSpec_image_top)).op x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x =>
        (M.map_smul (eqToHom (hU.fromSpec_image_top)) r x).trans
          (congrArg
            (fun s : Γ(X, hU.fromSpec ''ᵁ ⊤) =>
              s • (M.presheaf.map (eqToHom (hU.fromSpec_image_top)).op x))
            (congrArg (fun k : Γ(X, U) ⟶ Γ(X, hU.fromSpec ''ᵁ ⊤) => k.hom r)
              (map_eqToHom_fromSpec_image_top hU))) }

/-- Sections over an affine open `U` compared with the global sections over `Spec 𝒪_X(U)` of the
restriction, naturally in the sheaf of modules. -/
def affineSections : sectionsOver f U ⟶ globalSectionsRestrict hU where
  app M := affineSectionsApp f hU M
  naturality M N φ := by
    ext x
    exact (ConcreteCategory.congr_hom
      (φ.val.naturality (eqToHom (hU.fromSpec_image_top)).op) x).symm

/-- Taking global sections of `𝒪_{Spec 𝒪_X(U)}`-modules is additive: it is the right adjoint of
the associated-sheaf functor of Tag 01I7, which is additive. -/
instance additive_moduleSpecΓFunctor_sections :
    (moduleSpecΓFunctor (R := Γ(X, U))).Additive :=
  (tilde.adjunction (R := Γ(X, U))).right_adjoint_additive

/-- Restriction of sheaves of modules along `IsAffineOpen.fromSpec` is additive: it is a
reindexing of sections, so it is additive degreewise on the nose. -/
instance additive_restrictFunctor_fromSpec :
    (Scheme.Modules.restrictFunctor hU.fromSpec).Additive where
  map_add := rfl

/-- Taking sections over `U` is additive. -/
instance additive_sectionsOver : (sectionsOver f U).Additive where
  map_add := rfl

/-! ### The canonical map -/

/-- The canonical map of complexes of `𝒪_X(U)`-modules `L_{𝒪_X(U)/𝒪_Y(V)} ⟶ L_{X/Y}(U)`:
functoriality of the cotangent complex of a ring map along
`AlgebraicGeometry.Scheme.Hom.affineAlgebraSquare`, followed by the canonical map of
Remark 08SX on sections over `U`. -/
def cotangentSectionsComparison (e : U ≤ f ⁻¹ᵁ V) :
    CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e) ⟶
      ((sectionsOver f U).mapHomologicalComplex (ComplexShape.up ℤ)).obj f.cotangentComplex :=
  CommAlgCat.squareCotangentComplexMap.{u, u, u} (affineAlgebraSquare f e) ≫
    ((ModuleCat.restrictScalars (affineAlgebraSquare f e).map).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (CategoryTheory.Sheaf.sectionsCotangentComplexComparison.{u, u, u}
          (Opens.grothendieckTopology ↥X)
          (RingedToposHom.fSharpInverseImage f.zariskiRingedToposHom) (op U))

/-- `L_{X/Y}|_U`, the cotangent complex of `f` restricted to `U` along the identification of `U`
with `Spec 𝒪_X(U)`. -/
abbrev restrictedCotangentComplex :
    CochainComplex (Spec Γ(X, U)).Modules ℤ :=
  ((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj f.cotangentComplex

/-- The canonical map `L_{𝒪_X(U)/𝒪_Y(V)} ⟶ Γ(L_{X/Y}|_U)` of complexes of `𝒪_X(U)`-modules:
the comparison on sections over `U`, read through
`AlgebraicGeometry.Scheme.Hom.affineSections`. -/
def gammaCotangentComparison (e : U ≤ f ⁻¹ᵁ V) :
    CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e) ⟶
      ((moduleSpecΓFunctor (R := Γ(X, U))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictedCotangentComplex f hU) :=
  cotangentSectionsComparison f e ≫
    (NatTrans.mapHomologicalComplex (affineSections f hU) (ComplexShape.up ℤ)).app
      f.cotangentComplex

/-- **The canonical map of Tag 08T3.** For a morphism of schemes `f : X ⟶ Y`, an affine open
`U ⊂ X` with `B = 𝒪_X(U)` and an open `V ⊂ Y` with `f(U) ⊂ V` and `A = 𝒪_Y(V)`, the canonical
map `~(L_{B/A}) ⟶ L_{X/Y}|_U` of complexes of `𝒪_U`-modules: the adjunct, under the universal
property of the associated-sheaf functor (Tag 01I7), of the canonical map
`L_{B/A} ⟶ Γ(L_{X/Y}|_U)` of complexes of `B`-modules. -/
def affineCotangentComparison (e : U ≤ f ⁻¹ᵁ V) :
    ((tilde.functor Γ(X, U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} Γ(Y, V) (affineAlgebra f e)) ⟶
      restrictedCotangentComplex f hU :=
  ((tilde.functor Γ(X, U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (gammaCotangentComparison f hU e) ≫
    (NatTrans.mapHomologicalComplex
      (Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U)))
      (ComplexShape.up ℤ)).app (restrictedCotangentComplex f hU)

end AffineOpen

end AlgebraicGeometry.Scheme.Hom

end
