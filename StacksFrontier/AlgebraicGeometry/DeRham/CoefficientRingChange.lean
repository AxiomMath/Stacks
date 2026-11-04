module

public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle

/-!
# Change of coefficients from `(f ∘ g)^{-1}𝒪_S` to `f^{-1}𝒪_Y`

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. The space `X` carries two
inverse-image structure sheaves, `f^{-1}𝒪_Y` and `(f ∘ g)^{-1}𝒪_S`, and the canonical
homomorphism `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` between them makes the identity of `X` into a
morphism of ringed spaces

`(X, f^{-1}𝒪_Y) ⟶ (X, (f ∘ g)^{-1}𝒪_S)`

whose direct image on sheaves of modules is restriction of scalars along that homomorphism. That
restriction of scalars is what puts the two sides of the identification of the graded pieces of
Section 0FMK in one category: `gr^kΩ^•_{X/S}` is a complex of `(f ∘ g)^{-1}𝒪_S`-modules, while
`f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` is a complex of `f^{-1}𝒪_Y`-modules.

## Main definitions

* `Stacks.DeRhamDirectImage.coefficientRingChange`: **the morphism of ringed spaces
  `(X, f^{-1}𝒪_Y) ⟶ (X, (f ∘ g)^{-1}𝒪_S)`**, the identity on spaces and the canonical
  homomorphism `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` on structure sheaves.
* `Stacks.DeRhamDirectImage.coefficientRingCatHom`: that homomorphism as a morphism of sheaves
  of (not necessarily commutative) rings.
* `Stacks.DeRhamDirectImage.coefficientRestriction`: **the induced restriction of scalars
  `Mod(f^{-1}𝒪_Y) ⥤ Mod((f ∘ g)^{-1}𝒪_S)`**.

## Main results

* `Stacks.DeRhamDirectImage.toInverseImageBase_comp_coefficientRingChange`: **the triangle over
  `X`.** Reading an `𝒪_X`-module over `f^{-1}𝒪_Y` and then over `(f ∘ g)^{-1}𝒪_S` is reading it
  over `(f ∘ g)^{-1}𝒪_S`; `Stacks.DeRhamDirectImage.coefficientRestrictionToInverseImageBaseIso`
  is that statement on the three restriction-of-scalars functors.
* `Stacks.DeRhamDirectImage.coefficientRingChange_comp_inverseImageBaseProjection`: **the
  triangle over `S`**, which characterises the structure map: it is the unique one whose
  transpose along `(f ∘ g)^{-1} ⊣ (f ∘ g)_*` is `g^♯` followed by `g_*` of the unit of
  `f^{-1} ⊣ f_*`.
* `Stacks.DeRhamDirectImage.pushforward_coefficientRingChange`,
  `Stacks.DeRhamDirectImage.coefficientRestriction_obj` and
  `Stacks.DeRhamDirectImage.coefficientRestriction_map`: the induced functor is restriction of
  scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, on objects and on morphisms.
* `Stacks.DeRhamDirectImage.exactFunctor_coefficientRestriction`: the restriction of scalars is
  exact, and `Stacks.DeRhamDirectImage.additive_coefficientRestriction` additive; it does not
  change the underlying sheaf of abelian groups.

## Implementation notes

The homomorphism `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` is not built here. It is
`Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap`, constructed for morphisms of ringed
spaces as the middle map of the tower `(g ∘ f)^{-1}𝒪_Z ⟶ f^{-1}𝒪_Y ⟶ 𝒪_X` of [Stacks, Tag
08T4], and used here at the morphisms of ringed spaces underlying `f` and `g`; the triangle over
`X` is its `Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp`. The direct image of a
sheaf along a composite of continuous maps being the composite of the direct images *on the
nose*, no comparison of `(f ∘ g)^{-1}𝒪_S` with `f^{-1}g^{-1}𝒪_S` enters anywhere.

The two triangles are proved through `AlgebraicGeometry.PresheafedSpace.hext` rather than the
`ext` lemma, as `Stacks.DeRhamDirectImage.toInverseImageBase_comp` is: the base maps of their two
sides are `𝟙 ≫ 𝟙` and `𝟙`, and `𝟙 ≫ (f ∘ g)` and `f ≫ g`, definitionally but not syntactically
equal, and the `ext` lemma inserts an `eqToHom` along the proof of their equality which nothing
then removes.

Equality of the two composite direct images of the triangle over `X` is not available as a
rewrite — the direct image functor carries an additivity instance whose type mentions the
functor, so the rewrite motive is not type correct — so it is packaged as the isomorphism
`coefficientRestrictionToInverseImageBaseIso`, through
`Stacks.RingedSpace.pushforwardComp` and `CategoryTheory.eqToIso`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap baseStructureMap_comp)

universe u

namespace Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-! ### The morphism of ringed spaces -/

/-- **The coefficient-ring-change morphism `(X, f^{-1}𝒪_Y) ⟶ (X, (f ∘ g)^{-1}𝒪_S)`**: the
identity on spaces, with structure map the canonical homomorphism
`(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`. Its direct image on modules is restriction of scalars along that
homomorphism. -/
def coefficientRingChange : inverseImageBase f ⟶ inverseImageBase (f ≫ g) :=
  InducedCategory.homMk
    { base := 𝟙 X.carrier
      c := (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom }

/-- The coefficient-ring-change morphism is the identity on the underlying spaces. -/
@[simp]
theorem coefficientRingChange_base :
    (coefficientRingChange f g).hom.base = 𝟙 X.carrier := rfl

/-- The structure map of the coefficient-ring-change morphism is the canonical homomorphism
`(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`. -/
@[simp]
theorem coefficientRingChange_c :
    (coefficientRingChange f g).hom.c =
      (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom).hom := rfl

/-- **The triangle over `X`**: the identity-on-spaces morphism to `(X, f^{-1}𝒪_Y)` followed by
the coefficient-ring-change morphism is the identity-on-spaces morphism to
`(X, (f ∘ g)^{-1}𝒪_S)`. On structure sheaves this is the tower
`(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y ⟶ 𝒪_X` of [Stacks, Tag 08T4]. -/
theorem toInverseImageBase_comp_coefficientRingChange :
    toInverseImageBase f ≫ coefficientRingChange f g = toInverseImageBase (f ≫ g) := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  exact congrArg (fun t => t.hom)
    (baseStructureMap_comp f.toLRSHom.toShHom g.toLRSHom.toShHom)

/-- **The triangle over `S`**: the coefficient-ring-change morphism followed by the projection
of `(X, (f ∘ g)^{-1}𝒪_S)` to `S` is the projection of `(X, f^{-1}𝒪_Y)` to `Y` followed by `g`.
This characterises the structure map, being the statement that its transpose along
`(f ∘ g)^{-1} ⊣ (f ∘ g)_*` is `g^♯` followed by `g_*` of the unit of `f^{-1} ⊣ f_*`. -/
theorem coefficientRingChange_comp_inverseImageBaseProjection :
    coefficientRingChange f g ≫ inverseImageBaseProjection (f ≫ g) =
      inverseImageBaseProjection f ≫ g.toLRSHom.toShHom := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  have h := Equiv.apply_symm_apply
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f.base ≫ g.base)).homEquiv
      S.sheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf))
    ((⟨g.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Y.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app Y.sheaf))
  exact congrArg (fun t => t.hom) h

/-! ### Restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` -/

/-- The canonical homomorphism `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, read as a morphism of sheaves of
(not necessarily commutative) rings. -/
def coefficientRingCatHom :
    ringCatSheaf (inverseImageBase (f ≫ g)) ⟶ ringCatSheaf (inverseImageBase f) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
    (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)

/-- **Restriction of scalars `Mod(f^{-1}𝒪_Y) ⥤ Mod((f ∘ g)^{-1}𝒪_S)`**: the direct image along
the coefficient-ring-change morphism, the underlying map of spaces being the identity. -/
abbrev coefficientRestriction :
    Modules (inverseImageBase f) ⥤ Modules (inverseImageBase (f ≫ g)) :=
  pushforward (coefficientRingChange f g)

/-- **The direct image along the coefficient-ring-change morphism is restriction of scalars**
along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, the underlying map of spaces being the identity. -/
theorem pushforward_coefficientRingChange :
    pushforward (coefficientRingChange f g) =
      _root_.SheafOfModules.restrictScalars.{u, u, u, u} (coefficientRingCatHom f g) :=
  rfl

/-- **On objects** the restriction of scalars leaves the underlying presheaf of abelian groups
unchanged and only re-reads its module structure through `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`. -/
@[simp]
theorem coefficientRestriction_obj_val (M : Modules (inverseImageBase f)) :
    ((coefficientRestriction f g).obj M).val =
      (PresheafOfModules.restrictScalars (coefficientRingCatHom f g).hom).obj M.val :=
  rfl

/-- **On morphisms** the restriction of scalars leaves the underlying map of presheaves of
abelian groups unchanged. -/
@[simp]
theorem coefficientRestriction_map_val {M N : Modules (inverseImageBase f)} (φ : M ⟶ N) :
    ((coefficientRestriction f g).map φ).val =
      (PresheafOfModules.restrictScalars (coefficientRingCatHom f g).hom).map φ.val :=
  rfl

/-- Restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` is additive. -/
instance additive_coefficientRestriction : (coefficientRestriction f g).Additive :=
  RingedSpace.additive_restrictScalars (inverseImageBase f) (coefficientRingCatHom f g)

/-- **Restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` is exact**: it does not change
the underlying sheaf of abelian groups. -/
theorem exactFunctor_coefficientRestriction :
    PreservesFiniteLimits (coefficientRestriction f g) ∧
      PreservesFiniteColimits (coefficientRestriction f g) :=
  RingedSpace.exactFunctor_restrictScalars (inverseImageBase f) (coefficientRingCatHom f g)
    (RingedSpace.preservesFiniteColimits_toSheaf (inverseImageBase (f ≫ g)))

/-- Restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` is left exact. -/
instance preservesFiniteLimits_coefficientRestriction :
    PreservesFiniteLimits (coefficientRestriction f g) :=
  (exactFunctor_coefficientRestriction f g).1

/-- Restriction of scalars along `(f ∘ g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y` is right exact. -/
instance preservesFiniteColimits_coefficientRestriction :
    PreservesFiniteColimits (coefficientRestriction f g) :=
  (exactFunctor_coefficientRestriction f g).2

/-- **An `𝒪_X`-module read over `f^{-1}𝒪_Y` and then over `(f ∘ g)^{-1}𝒪_S` is the module read
over `(f ∘ g)^{-1}𝒪_S`**: the triangle over `X` on the three restrictions of scalars. -/
def coefficientRestrictionToInverseImageBaseIso :
    pushforward (toInverseImageBase f) ⋙ coefficientRestriction f g ≅
      pushforward (toInverseImageBase (f ≫ g)) :=
  (pushforwardComp (toInverseImageBase f) (coefficientRingChange f g)).symm ≪≫
    eqToIso (congrArg (fun m : X.toRingedSpace ⟶ inverseImageBase (f ≫ g) => pushforward m)
      (toInverseImageBase_comp_coefficientRingChange f g))

end Stacks.DeRhamDirectImage

end
