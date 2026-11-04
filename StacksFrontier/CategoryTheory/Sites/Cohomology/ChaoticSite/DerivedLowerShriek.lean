module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedChangeOfCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek with coefficients in a sheaf of rings on a chaotic site

Let `C` be a small category with the chaotic topology, let `B` be a ring and let `O` be a sheaf
of rings on `C` together with a map `φ : O ⟶ B̲` to the constant sheaf of rings. Stacks 09CZ
produces from this an exact functor of triangulated categories
`Lπ_! : D(O) ⟶ D(B)`,
namely the composite of derived extension of scalars `- ⊗^L_O B̲` with derived lower shriek
`Lπ_! : D(B̲) ⟶ D(B)`.

Both factors are left adjoints: extension of scalars along `φ` is left adjoint to restriction
of scalars (Stacks 03CZ) and lower shriek is left adjoint to inverse image, which on a chaotic
site is the colimit over `Cᵒᵖ` and the constant diagram (Stacks 08PF). Both have total left
derived functors by Stacks 0794 at the projective objects, and the resulting derived adjunctions
compose. Its left adjoint therefore commutes with the shift and is exact, which is the assertion
of 09CZ; those two facts are `Adjunction.leftAdjointCommShift` and
`Adjunction.isTriangulated_leftAdjoint` applied to the composite derived adjunction.

On the chaotic topology every presheaf is a sheaf, so `O`-modules are presheaves of modules over
the underlying presheaf of rings (`Stacks.ChaoticSite.moduleSheafPresheafEquivalence`) and
`B̲`-modules are diagrams of `B`-modules on `Cᵒᵖ`
(`Stacks.ChaoticSite.constantModulePresheafEquivalence`); the statements below are read in that
presentation, as are those of Stacks 08Q6, 08Q7 and 08Q8.

## Main definitions

* `Stacks.ChaoticSite.trivialSheafOfRings` and
  `Stacks.ChaoticSite.moduleSheafPresheafEquivalence`: on a chaotic site a presheaf of rings is
  a sheaf of rings and its presheaves of modules are its sheaves of modules.
* `Stacks.ChaoticSite.constantModulePresheafEquivalence`: presheaves of modules over a constant
  presheaf of rings are diagrams of modules.
* `Stacks.ChaoticSite.constantSectionsModulePresheaf`: the presheaf of modules over a constant
  presheaf of rings with constant sections `M` and identity restriction maps, with
  `Stacks.ChaoticSite.constantSectionsModulePresheafIso` identifying it with the image of the
  constant diagram `M̲` under the inverse of the equivalence.
* `Stacks.ChaoticSite.coefficientExtension` and `Stacks.ChaoticSite.coefficientRestriction`:
  extension and restriction of scalars along `φ`, the second read on diagrams of `B`-modules,
  with their adjunction `Stacks.ChaoticSite.coefficientAdjunction`.
* `Stacks.ChaoticSite.derivedCoefficientExtension`: the total left derived functor
  `- ⊗^L_O B̲`, with its derived adjunction.
* `Stacks.ChaoticSite.derivedColimitWithCoefficients`: **Stacks 09CZ**, the functor
  `Lπ_! : D(O) ⟶ D(B)`.

## Main results

* `PresheafOfModules.freeYonedaProjective` and `PresheafOfModules.enoughProjectives`: the free
  presheaf of modules on a representable presheaf is projective, and a category of presheaves of
  modules over a small site has enough projectives.
* `PresheafOfModules.hasExactColimitsOfShapeNat`: countable filtered colimits of presheaves of
  modules are exact.
* `Stacks.ChaoticSite.derivedColimitWithCoefficients_commShift` and
  `Stacks.ChaoticSite.derivedColimitWithCoefficients_isTriangulated`: **Stacks 09CZ**, the
  functor is exact as a functor of triangulated categories.

## Implementation notes

The hypothesis of the source statement that `φ` induce an isomorphism `Lπ_!O ⟶ Lπ_!B̲` is *not*
assumed: the composite functor and its exactness do not depend on it. What that hypothesis buys
is the identification of this functor with lower shriek of the underlying abelian sheaves, which
is Stacks 08RX and is a different assertion; the construction and its exactness are proved here
for an arbitrary coefficient map, which is the generality the source itself notes.

The site, the ring and the module sections live in one universe `u`. That is forced from two
sides, and not by the argument: Mathlib's resolution of a presheaf of modules by free presheaves
on representables (`PresheafOfModules.fromFreeYonedaCoproduct`, the source of enough
projectives) and the existence of presheaf-level extension of scalars
(`Stacks.SheafOfModules.ChangeOfRings.presheafRestrictScalars_isRightAdjoint`) both require a
small site whose universe is that of the rings and of the modules.

## References

* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

universe u

variable {C : Type u} [SmallCategory C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The free presheaf of modules on a representable presheaf is projective.** Maps out of it
are the sections over the representing object, and an epimorphism of presheaves of modules is
surjective on sections. -/
@[sga "4 V 2.3.1"]
instance freeYonedaProjective (X : C) : Projective ((free R).obj (yoneda.obj X)) where
  factors {_ _} g e he := by
    have := he
    obtain ⟨y, hy⟩ := surjective_of_epi e (Opposite.op X) (freeYonedaEquiv g)
    refine ⟨freeYonedaEquiv.symm y, ?_⟩
    apply freeYonedaEquiv.injective
    rwa [freeYonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **Presheaves of modules over a small site have enough projectives**: every presheaf of
modules receives an epimorphism from the coproduct, indexed by its sections, of the free
presheaves of modules on the representables, and that coproduct is projective. -/
instance enoughProjectives : EnoughProjectives (PresheafOfModules.{u} R) :=
  ⟨fun M => ⟨{ p := M.freeYonedaCoproduct, f := M.fromFreeYonedaCoproduct }⟩⟩

/-- **Countable filtered colimits of presheaves of modules are exact**, since they are computed
on the underlying presheaves of abelian groups, where this is Grothendieck's axiom AB5. -/
instance hasExactColimitsOfShapeNat :
    HasExactColimitsOfShape ℕ (PresheafOfModules.{u} R) :=
  HasExactColimitsOfShape.domain_of_functor ℕ (toPresheaf R)

/-- **Restriction of scalars for presheaves of modules is exact**: it does not change the
underlying presheaf of abelian groups, where exactness is tested. -/
instance restrictScalars_preservesHomology (φ : R ⟶ R') :
    (restrictScalars.{u} φ).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  apply (toPresheaf R).reflects_exact_of_faithful
  exact hS.map (toPresheaf R')

/-- Restriction of scalars for presheaves of modules is left exact. -/
instance restrictScalars_preservesFiniteLimits (φ : R ⟶ R') :
    PreservesFiniteLimits (restrictScalars.{u} φ) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Restriction of scalars for presheaves of modules is right exact. -/
instance restrictScalars_preservesFiniteColimits (φ : R ⟶ R') :
    PreservesFiniteColimits (restrictScalars.{u} φ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end PresheafOfModules

namespace Stacks.ChaoticSite

universe u

open Stacks.CategoryHomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Modules on a chaotic site -/

section Chaotic

variable {C : Type u} [SmallCategory C]

/-- A presheaf of rings on a chaotic site, read as a sheaf of rings: for the chaotic topology
every presheaf is a sheaf. This is the object-level form of
`Stacks.ChaoticSite.trivialTopologySheafEquivalence`. -/
def trivialSheafOfRings (R : Cᵒᵖ ⥤ RingCat.{u}) :
    Sheaf (GrothendieckTopology.trivial C) RingCat.{u} :=
  ⟨R, by simpa only [GrothendieckTopology.trivial_eq_bot] using Presheaf.isSheaf_bot R⟩

/-- **On a chaotic site, sheaves of modules over a presheaf of rings are its presheaves of
modules**: forgetting the sheaf condition is an equivalence. -/
def moduleSheafPresheafEquivalence (R : Cᵒᵖ ⥤ RingCat.{u}) :
    SheafOfModules.{u} (trivialSheafOfRings (C := C) R) ≌ PresheafOfModules.{u} R where
  functor := SheafOfModules.forget _
  inverse :=
    { obj M := ⟨M, by simpa only [GrothendieckTopology.trivial_eq_bot] using
        Presheaf.isSheaf_bot _⟩
      map f := ⟨f⟩ }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- **Presheaves of modules over a constant presheaf of rings are diagrams of modules.** This
is `Stacks.ChaoticSite.constantModuleSheafEquivalence`, read on presheaves of modules through
`Stacks.ChaoticSite.moduleSheafPresheafEquivalence`. -/
def constantModulePresheafEquivalence (B : Type u) [Ring B] :
    PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)) ≌
      (Cᵒᵖ ⥤ ModuleCat.{u} B) :=
  (moduleSheafPresheafEquivalence ((Functor.const Cᵒᵖ).obj (RingCat.of B))).symm.trans
    (constantModuleSheafEquivalence (RingCat.of B) _ rfl)

/-- **The diagram of modules attached to a presheaf of modules over a constant presheaf of rings
is any diagram with the same sections and the same restriction maps.** This is
`Stacks.ChaoticSite.constantModuleSheafEquivalenceFunctorObjIso` read on presheaves of modules;
like it, it exists because the equivalence is assembled from definitions that are reducible only
where they are given, so that a consumer cannot otherwise see that the sections of
`(constantModulePresheafEquivalence B).functor.obj G` are those of `G`. -/
def constantModulePresheafEquivalenceFunctorObjIso (B : Type u) [Ring B]
    (G : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
    (D : Cᵒᵖ ⥤ ModuleCat.{u} B) (e : ∀ V, G.obj V ≅ D.obj V)
    (he : ∀ {V W : Cᵒᵖ} (g : V ⟶ W) (x : G.obj V),
      (e W).hom (G.map g x) = D.map g ((e V).hom x)) :
    (constantModulePresheafEquivalence (C := C) B).functor.obj G ≅ D :=
  constantModuleSheafEquivalenceFunctorObjIso (RingCat.of B) _ _ D e he

/-- **The presheaf of modules over a constant presheaf of rings with constant sections `M` and
identity restriction maps.** It is the object of
`PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of B))` that
`Stacks.ChaoticSite.constantModulePresheafEquivalence` attaches to the constant diagram `M̲`,
with its sections written out; the identification is
`Stacks.ChaoticSite.constantSectionsModulePresheafIso`. -/
@[expose] def constantSectionsModulePresheaf (B : Type u) [Ring B] (M : ModuleCat.{u} B) :
    PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of B)) where
  obj _ := M
  map _ := 𝟙 M

/-- **The presheaf of modules over `B̲` that
`Stacks.ChaoticSite.constantModulePresheafEquivalence` attaches to the constant diagram `M̲` has
constant sections `M`.** The equivalence is reducible only where it is given, so the
identification is obtained from its unit instead:
`Stacks.ChaoticSite.constantSectionsModulePresheaf` is carried to the constant diagram `M̲` by
`Stacks.ChaoticSite.constantModulePresheafEquivalenceFunctorObjIso`, and an equivalence takes an
isomorphism of images to an isomorphism of the objects. -/
def constantSectionsModulePresheafIso (B : Type u) [Ring B] (M : ModuleCat.{u} B) :
    constantSectionsModulePresheaf (C := C) B M ≅
      (constantModulePresheafEquivalence (C := C) B).inverse.obj ((Functor.const _).obj M) :=
  (constantModulePresheafEquivalence (C := C) B).unitIso.app
      (constantSectionsModulePresheaf (C := C) B M) ≪≫
    (constantModulePresheafEquivalence (C := C) B).inverse.mapIso
      (constantModulePresheafEquivalenceFunctorObjIso (C := C) B
        (constantSectionsModulePresheaf (C := C) B M) ((Functor.const _).obj M)
        (fun _ => Iso.refl M) (fun _ _ => rfl))

/-- The functor of `Stacks.ChaoticSite.constantModulePresheafEquivalence` is additive. -/
instance constantModulePresheafEquivalence_additive (B : Type u) [Ring B] :
    (constantModulePresheafEquivalence (C := C) B).functor.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts
    (constantModulePresheafEquivalence (C := C) B).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The inverse of `Stacks.ChaoticSite.constantModulePresheafEquivalence` is additive. -/
instance constantModulePresheafEquivalence_inverse_additive (B : Type u) [Ring B] :
    (constantModulePresheafEquivalence (C := C) B).inverse.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts
    (constantModulePresheafEquivalence (C := C) B).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-! ### Stacks 09CZ -/

variable (B : Type u) [Ring B] (O : Cᵒᵖ ⥤ RingCat.{u})
  (φ : O ⟶ (Functor.const Cᵒᵖ).obj (RingCat.of B))

/-- Extension of scalars along the coefficient map `φ : O ⟶ B̲`, with its target read as
diagrams of `B`-modules: informally `M ↦ M ⊗_O B̲`. -/
abbrev coefficientExtension : PresheafOfModules.{u} O ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} B) :=
  (PresheafOfModules.restrictScalars.{u} φ).leftAdjoint ⋙
    (constantModulePresheafEquivalence B).functor

/-- Restriction of scalars along the coefficient map `φ : O ⟶ B̲`: a diagram of `B`-modules read
as an `O`-module. -/
abbrev coefficientRestriction : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ PresheafOfModules.{u} O :=
  (constantModulePresheafEquivalence B).inverse ⋙ PresheafOfModules.restrictScalars.{u} φ

/-- **Stacks 03CZ for the coefficient map**: extension of scalars along `φ` is left adjoint to
restriction of scalars along `φ`. -/
abbrev coefficientAdjunction : coefficientExtension B O φ ⊣ coefficientRestriction B O φ :=
  (Adjunction.ofIsRightAdjoint (PresheafOfModules.restrictScalars.{u} φ)).comp
    (constantModulePresheafEquivalence B).toAdjunction

/-- Extension of scalars along the coefficient map `φ : O ⟶ B̲` is additive. -/
instance coefficientExtension_additive : (coefficientExtension B O φ).Additive :=
  (coefficientAdjunction B O φ).left_adjoint_additive

/-- **Derived extension of scalars along the coefficient map**, `- ⊗^L_O B̲`. It exists
unconditionally: extension of scalars is a right exact left adjoint out of a category of
presheaves of modules, which has enough projectives. -/
def derivedCoefficientExtension :
    DerivedCategory (PresheafOfModules.{u} O) ⥤ DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} B) :=
  totalDerivedLeftAdjoint (coefficientExtension B O φ)

/-- Derived extension of scalars is left adjoint to the degreewise derived restriction of
scalars. -/
def derivedCoefficientExtensionAdjunction :
    derivedCoefficientExtension B O φ ⊣ (coefficientRestriction B O φ).mapDerivedCategory :=
  totalDerivedLeftAdjointAdjunction _ (coefficientAdjunction B O φ)

/-- **Stacks 09CZ.** For a map `φ : O ⟶ B̲` from a sheaf of rings on a chaotic site to the
constant sheaf of rings of a ring `B`, derived lower shriek with coefficients in `O` is the
functor `Lπ_! : D(O) ⟶ D(B)` obtained by composing derived extension of scalars
`- ⊗^L_O B̲` with derived lower shriek `D(B̲) ⟶ D(B)`. -/
@[stacks 09CZ "derived_colimit_with_b_coefficients_2"]
def derivedColimitWithCoefficients :
    DerivedCategory (PresheafOfModules.{u} O) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  derivedCoefficientExtension B O φ ⋙ totalDerivedColimit C (ModuleCat.{u} B)

/-- Derived lower shriek with coefficients is a left adjoint, being the composite of the two
derived adjunctions it is built from. -/
def derivedColimitWithCoefficientsAdjunction :
    derivedColimitWithCoefficients B O φ ⊣
      (Functor.const Cᵒᵖ : ModuleCat.{u} B ⥤ _).mapDerivedCategory ⋙
        (coefficientRestriction B O φ).mapDerivedCategory :=
  (derivedCoefficientExtensionAdjunction B O φ).comp
    (totalDerivedColimitAdjunction C (ModuleCat.{u} B))

/-- **Stacks 09CZ**: derived lower shriek with coefficients commutes with the shift, being a
left adjoint of a functor that does. -/
@[stacks 09CZ "derived_colimit_with_b_coefficients_exact"]
instance derivedColimitWithCoefficients_commShift :
    (derivedColimitWithCoefficients B O φ).CommShift ℤ :=
  (derivedColimitWithCoefficientsAdjunction B O φ).leftAdjointCommShift ℤ

/-- **Stacks 09CZ**: derived lower shriek with coefficients is an exact functor of triangulated
categories `D(O) ⟶ D(B)`. -/
@[stacks 09CZ "derived_colimit_with_b_coefficients_exact"]
instance derivedColimitWithCoefficients_isTriangulated :
    (derivedColimitWithCoefficients B O φ).IsTriangulated :=
  have : (derivedColimitWithCoefficientsAdjunction B O φ).CommShift ℤ :=
    (derivedColimitWithCoefficientsAdjunction B O φ).commShift_of_rightAdjoint ℤ
  (derivedColimitWithCoefficientsAdjunction B O φ).isTriangulated_leftAdjoint

end Chaotic

end Stacks.ChaoticSite

end
