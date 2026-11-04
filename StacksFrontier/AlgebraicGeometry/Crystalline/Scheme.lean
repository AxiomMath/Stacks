module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Divided power schemes

Let `O` be a sheaf of commutative rings on a site and let `I` be a sheaf of ideals in `O`.  A
divided power structure on `I` is a divided power structure on every ring of sections `I(U)`,
compatible with all restriction maps; equivalently, it makes the rings of sections of `O` into a
presheaf of divided power rings whose ideals are the sections of `I`.

A divided power scheme is a scheme `X` together with a quasi-coherent sheaf of ideals in `O_X`
and a divided power structure on it.  A morphism of divided power schemes is a morphism of
schemes whose maps on sections carry the target ideal into the source ideal and commute with all
divided power operations.  Divided power schemes form a category.

## Main definitions

* `Crystalline.DividedPowerStructure` — a divided power structure on a sheaf of ideals.
* `Crystalline.DividedPowerScheme` — a scheme with a quasi-coherent divided power ideal.
* `Crystalline.DividedPowerScheme.Hom` — a morphism compatible with the divided power ideals.

## Main results

* `Crystalline.DividedPowerStructure.restrict_dpow` — divided powers commute with restriction.
* `Crystalline.DividedPowerStructure.toPresheaf` — the rings of sections of a divided power
  ideal sheaf form a presheaf of divided power rings.
* `Crystalline.DividedPowerScheme.Hom.toDPMorphism` — the homomorphism of divided power rings
  induced on the sections over an open subset of the target.
* `Crystalline.DividedPowerScheme.instCategory` — divided power schemes and their compatible
  morphisms form a category.
* `Crystalline.globalSectionsDPMorphism` — the contravariant action of a morphism on the divided
  power rings of global sections.

## Implementation notes

A sheaf of ideals in `O` is represented by Mathlib's `SheafOfModules.Submodule` of the rank-one
module over the underlying sheaf of rings, so that its associated sheaf of modules and the
existing locality, restriction and lattice API are directly available; for a scheme,
quasi-coherence is then asserted of that associated sheaf of modules.  Mathlib's divided power
operations are indexed by all natural numbers and take values in the ambient ring;
`DividedPowerStructure.dpow` restricts the positive-indexed operations to maps of the ideal.
Compatibility with restriction, and the compatibility condition on a morphism of divided power
schemes, are both expressed by `DividedPowers.IsDPMorphism`, so that every restriction map and
every map on sections is canonically a morphism of the divided power rings of sections.

## References

* [Stacks Project, Tag 07I2](https://stacks.math.columbia.edu/tag/07I2)
* [Stacks Project, Tag 07I3](https://stacks.math.columbia.edu/tag/07I3)
-/

@[expose] public section

namespace Crystalline

/-- Divided power compatibility of a ring homomorphism depends only on the homomorphism, so it
transports along an equality of homomorphisms. -/
public theorem isDPMorphism_of_eq {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}
    {J : Ideal B} {hI : DividedPowers I} {hJ : DividedPowers J} {f g : A →+* B} (h : f = g)
    (hf : DividedPowers.IsDPMorphism hI hJ f) : DividedPowers.IsDPMorphism hI hJ g :=
  h ▸ hf


section IdealSheaf

open CategoryTheory Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Regard a sheaf of commutative rings as a sheaf of rings. -/
public noncomputable abbrev ringSheaf (O : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O

/-- The ideal of sections over `U` underlying an ideal subsheaf of `O`. -/
public noncomputable abbrev sectionIdeal (O : Sheaf J CommRingCat.{w})
    (I : (SheafOfModules.unit (ringSheaf O)).Submodule) (U : Cᵒᵖ) :
    Ideal (O.obj.obj U) :=
  I.obj U

/-- Identify the objectwise ideal with the sections of the associated sheaf of modules. -/
public noncomputable def sectionIdealEquiv (O : Sheaf J CommRingCat.{w})
    (I : (SheafOfModules.unit (ringSheaf O)).Submodule) (U : Cᵒᵖ) :
    sectionIdeal O I U ≃+ I.toSheafOfModules.val.obj U :=
  AddEquiv.refl _

/-- A divided power structure on a sheaf of ideals: every ideal of sections has divided powers,
and every restriction map is compatible with them. -/
@[stacks 07I2]
public structure DividedPowerStructure (O : Sheaf J CommRingCat.{w})
    (I : (SheafOfModules.unit (ringSheaf O)).Submodule) where
  /-- The divided power structure on the ideal of sections over `U`. -/
  dividedPowers (U : Cᵒᵖ) : DividedPowers (sectionIdeal O I U)
  /-- Restriction maps commute with all divided power operations. -/
  naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    DividedPowers.IsDPMorphism (dividedPowers U) (dividedPowers V) (O.obj.map f).hom

namespace DividedPowerStructure

/-- The divided power ring of sections over an object of the site. -/
public def toDividedPowerRing {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) (U : Cᵒᵖ) : DividedPowerRing where
  carrier := O.obj.obj U
  ideal := I.obj U
  dividedPowers := gamma.dividedPowers U

/-- A restriction map regarded as a morphism of divided power rings. -/
public def restriction {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) {U V : Cᵒᵖ} (f : U ⟶ V) :
    gamma.toDividedPowerRing U ⟶ gamma.toDividedPowerRing V :=
  DividedPowers.DPMorphism.mk' (gamma.naturality f)

/-- The underlying function of restriction is the restriction map of the ring sheaf. -/
@[simp]
public theorem restriction_apply {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : O.obj.obj U) : gamma.restriction f x = O.obj.map f x := rfl

/-- The rings of sections of a divided power ideal sheaf form a presheaf of divided power
rings. -/
@[implicit_reducible]
public def toPresheaf {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) : Cᵒᵖ ⥤ DividedPowerRing where
  obj U := gamma.toDividedPowerRing U
  map f := gamma.restriction f
  map_id X := by
    ext x
    change O.obj.map (𝟙 X) x = x
    simp
    rfl
  map_comp f g := by
    ext x
    change O.obj.map (f ≫ g) x = O.obj.map g (O.obj.map f x)
    simp
    rfl

/-- Restriction of a section of the ideal subsheaf, in its objectwise-ideal presentation. -/
public def restrict {O : Sheaf J CommRingCat.{w}}
    (I : (SheafOfModules.unit (ringSheaf O)).Submodule)
    {U V : Cᵒᵖ} (f : U ⟶ V) : sectionIdeal O I U → sectionIdeal O I V :=
  fun x ↦ ⟨O.obj.map f x, by
    change O.obj.map f x ∈ I.obj V
    exact I.toSubmodule.map_mem f x.2⟩

/-- Restriction in the objectwise ideal has the expected underlying ring section. -/
@[simp]
public theorem coe_restrict {O : Sheaf J CommRingCat.{w}}
    (I : (SheafOfModules.unit (ringSheaf O)).Submodule)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : sectionIdeal O I U) :
    (restrict I f x : O.obj.obj V) = O.obj.map f x := rfl

/-- Objectwise restriction agrees with restriction in the associated sheaf of modules. -/
@[simp]
public theorem sectionIdealEquiv_restrict {O : Sheaf J CommRingCat.{w}}
    (I : (SheafOfModules.unit (ringSheaf O)).Submodule)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : sectionIdeal O I U) :
    sectionIdealEquiv O I V (restrict I f x) =
      I.toSheafOfModules.val.map f (sectionIdealEquiv O I U x) := by
  apply Subtype.ext
  rfl

/-- The positive-indexed divided power operation as a map from the ideal to itself. -/
public def dpow {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) (n : ℕ) (hn : n ≠ 0) (U : Cᵒᵖ) :
    sectionIdeal O I U → sectionIdeal O I U :=
  fun x ↦ ⟨(gamma.dividedPowers U).dpow n x,
    (gamma.dividedPowers U).dpow_mem hn x.2⟩

/-- The ideal-valued divided power operation has the expected underlying section. -/
@[simp]
public theorem coe_dpow {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) (n : ℕ) (hn : n ≠ 0) (U : Cᵒᵖ)
    (x : sectionIdeal O I U) :
    (gamma.dpow n hn U x : O.obj.obj U) = (gamma.dividedPowers U).dpow n x := rfl

/-- Divided power operations on the ideal commute with the restriction maps of its associated
sheaf of modules. -/
@[simp]
public theorem restrict_dpow {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    (gamma : DividedPowerStructure O I) (n : ℕ) (hn : n ≠ 0)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : sectionIdeal O I U) :
    restrict I f (gamma.dpow n hn U x) =
      gamma.dpow n hn V (restrict I f x) :=
  Subtype.ext ((gamma.naturality f).map_dpow x.2)

/-- Two divided power structures on an ideal sheaf are equal if their structures on all rings of
sections are equal. -/
@[ext]
public theorem ext {O : Sheaf J CommRingCat.{w}}
    {I : (SheafOfModules.unit (ringSheaf O)).Submodule}
    {gamma delta : DividedPowerStructure O I}
    (h : ∀ U, gamma.dividedPowers U = delta.dividedPowers U) : gamma = delta := by
  cases gamma with
  | mk gamma hgamma =>
    cases delta with
    | mk delta hdelta =>
      dsimp at h
      have : gamma = delta := funext h
      subst delta
      rfl

end DividedPowerStructure

end IdealSheaf

section Scheme

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-- A scheme equipped with a quasi-coherent sheaf of ideals and a divided power structure on
that ideal. -/
@[stacks 07I3 "divided power schemes"]
public structure DividedPowerScheme where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}
  /-- The quasi-coherent ideal sheaf, presented as an ideal submodule of the structure sheaf. -/
  ideal : (SheafOfModules.unit scheme.ringCatSheaf).Submodule
  /-- The ideal sheaf is quasi-coherent. -/
  isQuasicoherent : ideal.toSheafOfModules.IsQuasicoherent
  /-- The divided power structure on the ideal sheaf. -/
  dividedPowers : DividedPowerStructure.{u, u, u} scheme.sheaf ideal

namespace DividedPowerScheme

/-- The quasi-coherence carried by the ideal of a divided power scheme. -/
public instance (X : DividedPowerScheme.{u}) :
    X.ideal.toSheafOfModules.IsQuasicoherent := X.isQuasicoherent

/-- A morphism of divided power schemes. On each open subset of the target, the induced map on
sections is a homomorphism of divided power rings. In particular, it maps the target ideal into
the source ideal. -/
@[ext, stacks 07I3 "morphisms of divided power schemes"]
public structure Hom (X Y : DividedPowerScheme.{u}) where
  /-- The underlying morphism of schemes. -/
  hom : X.scheme ⟶ Y.scheme
  /-- The maps on sections preserve the divided power ideals and their divided powers. -/
  compatible (U : Y.scheme.Opens) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (hom ⁻¹ᵁ U))) (hom.app U).hom

namespace Hom

/-- The homomorphism of divided power rings induced on sections over an open subset. -/
@[implicit_reducible]
public def toDPMorphism {X Y : DividedPowerScheme.{u}} (f : Hom X Y) (U : Y.scheme.Opens) :
    DividedPowers.DPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (f.hom ⁻¹ᵁ U))) :=
  DividedPowers.DPMorphism.mk' (f.compatible U)

/-- The induced divided power morphism agrees on sections with the underlying scheme morphism. -/
@[simp]
public theorem toDPMorphism_apply {X Y : DividedPowerScheme.{u}} (f : Hom X Y)
    (U : Y.scheme.Opens) (a : Y.scheme.sheaf.obj.obj (op U)) :
    f.toDPMorphism U a = f.hom.app U a := rfl

/-- The underlying ring homomorphism on sections. -/
@[simp]
public theorem toDPMorphism_toRingHom {X Y : DividedPowerScheme.{u}} (f : Hom X Y)
    (U : Y.scheme.Opens) : (f.toDPMorphism U).toRingHom = (f.hom.app U).hom := rfl

/-- The image of the target ideal on an open subset is contained in the source ideal over its
preimage. -/
public theorem ideal_comp {X Y : DividedPowerScheme.{u}} (f : Hom X Y) (U : Y.scheme.Opens) :
    (sectionIdeal Y.scheme.sheaf Y.ideal (op U)).map (f.hom.app U).hom ≤
      sectionIdeal X.scheme.sheaf X.ideal (op (f.hom ⁻¹ᵁ U)) :=
  (f.compatible U).ideal_comp

/-- The maps on sections commute with every divided power operation. -/
public theorem dpow_comp {X Y : DividedPowerScheme.{u}} (f : Hom X Y) (U : Y.scheme.Opens)
    {n : ℕ} (a : Y.scheme.sheaf.obj.obj (op U)) (ha : a ∈ Y.ideal.obj (op U)) :
    (X.dividedPowers.dividedPowers (op (f.hom ⁻¹ᵁ U))).dpow n (f.hom.app U a) =
      f.hom.app U ((Y.dividedPowers.dividedPowers (op U)).dpow n a) :=
  (f.compatible U).dpow_comp a ha

end Hom

/-- Divided power schemes and their compatible morphisms form a category. -/
public instance : Category.{u} DividedPowerScheme where
  Hom := Hom
  id X :=
    { hom := 𝟙 X.scheme
      compatible U := by
        convert (DividedPowers.DPMorphism.id
          (X.dividedPowers.dividedPowers (op U))).isDPMorphism using 1
        rfl }
  comp {X Y Z} f g :=
    { hom := f.hom ≫ g.hom
      compatible U := by
        convert (DividedPowers.IsDPMorphism.comp
          (X.dividedPowers.dividedPowers (op (f.hom ⁻¹ᵁ g.hom ⁻¹ᵁ U)))
          (f.compatible (g.hom ⁻¹ᵁ U)) (g.compatible U)) using 1
        rfl }
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

namespace Hom

/-- The underlying scheme morphism of the categorical identity. -/
@[simp]
public theorem id_hom (X : DividedPowerScheme.{u}) : (𝟙 X : X ⟶ X).hom = 𝟙 X.scheme := rfl

/-- The underlying scheme morphism of a categorical composite. -/
@[simp]
public theorem comp_hom {X Y Z : DividedPowerScheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

end Hom

end DividedPowerScheme

/-- The morphism of divided power rings induced on global sections by a morphism of divided power
schemes.  Global sections reverse the direction. -/
public def globalSectionsDPMorphism {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) :
    Y.dividedPowers.toDividedPowerRing (op ⊤) ⟶ X.dividedPowers.toDividedPowerRing (op ⊤) :=
  f.toDPMorphism ⊤

/-- The ring map underlying `globalSectionsDPMorphism f` is the map `f.hom.appTop` on global
sections. -/
@[simp]
public theorem globalSectionsDPMorphism_toRingHom {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) :
    (globalSectionsDPMorphism f).toRingHom = f.hom.appTop.hom := rfl

/-- Global sections turn a composite of morphisms of divided power schemes into the composite of
the induced morphisms of divided power rings, in the opposite order. -/
public theorem globalSectionsDPMorphism_comp {X Y Z : DividedPowerScheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (globalSectionsDPMorphism f).comp (globalSectionsDPMorphism g) =
      globalSectionsDPMorphism (f ≫ g) :=
  DividedPowers.DPMorphism.ext (congrArg (fun h : CommRingCat.of Γ(Z.scheme, ⊤) ⟶
    CommRingCat.of Γ(X.scheme, ⊤) ↦ (h.hom : Γ(Z.scheme, ⊤) → Γ(X.scheme, ⊤)))
      (Scheme.Γ.map_comp g.hom.op f.hom.op)).symm

/-- Global sections take the identity to the identity. -/
public theorem globalSectionsDPMorphism_id (X : DividedPowerScheme.{u}) :
    globalSectionsDPMorphism (𝟙 X) = 𝟙 (X.dividedPowers.toDividedPowerRing (op ⊤)) := by
  apply DividedPowers.DPMorphism.ext
  rfl

end

end Scheme

end Crystalline

end
