module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardNormalizedIso
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSectionTransportCoherence
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs

/-!
# The rigidified Picard stack is fibred in setoids (Stacks 0D2B)

In Situation 0D25, let `σ : B ⟶ X` be a section of `f : X ⟶ B` and assume that
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T` over `B`
(`AlgebraicGeometry.Space.PicardSituation.StructureSheafMapIso`).  Stacks 0D2B asserts that
`Picardstack_{X/B, σ} ⟶ (Sch/S)_{fppf}` is then fibred in setoids, and that its set of
isomorphism classes over a scheme `T` is
`∐_{h : T ⟶ B} Ker(σ_T^* : Pic(X ×_{B, h} T) ⟶ Pic(T))`.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.kernelObject`: the object `(T, h, L, α)` of
  `Picardstack_{X/B, σ}` attached to an element `[L]` of `Ker(σ_T^*)`, with a chosen
  representative `L` and a chosen trivialisation `α` along `σ_T`.
* `AlgebraicGeometry.Space.sectionedPicardIsoClassEquiv`: **the bijection of Stacks 0D2B**
  between the isomorphism classes of the fibre of `Picardstack_{X/B, σ}` over `T` and
  `∐_{h : T ⟶ B} Ker(σ_T^*)`; it sends the class of `(T, h, L, α)` to `(h, [L])`.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.picardHom_eq_of_transportTrivialization_eq`: two
  morphisms of `Picardstack_{X/B}` with the same base which transport a trivialisation to the
  same trivialisation agree.  This is the source's "an automorphism is multiplication by a unit
  `u` with `σ_T^*u = 1`, hence `u = 1`".
* `AlgebraicGeometry.Space.PicardSituation.exists_sectionedPicardHom`: a morphism of
  `Picardstack_{X/B}` between the underlying triples of two objects of
  `Picardstack_{X/B, σ}` can be renormalised into a morphism of `Picardstack_{X/B, σ}` with the
  same base.  This is the source's "any two choices of `α` differ by a global unit on `T`, and
  this is the same thing as a global unit on `X_T`".
* `AlgebraicGeometry.Space.sectionedPicardProjection_isFiberedInSetoids`: `Picardstack_{X/B, σ}`
  is fibred in setoids.
* `AlgebraicGeometry.Space.sectionedPicardCFG_isFiberedInSetoids_and_isoClassEquiv`: both
  conclusions of Stacks 0D2B together, for `Picardstack_{X/B, σ}` built from the canonical
  data; `..._of_coherence` states them for any choice of the two coherence inputs.

## Implementation notes

**Where the hypothesis is used.**  Both halves rest on
`AlgebraicGeometry.Space.PicardSituation.bijective_sectionPullback_map`: when
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism, restriction along `σ_T` is bijective on the
homomorphisms between two isomorphic invertible `𝒪_{X_T}`-modules.  Injectivity gives the
uniqueness of automorphisms (fibred in setoids), and surjectivity lets an isomorphism of
modules be rescaled so as to match two prescribed trivialisations (objects with the same class
are isomorphic).  No group of units is named: the units `u` of the source are the
automorphisms of the invertible modules, and the hypothesis enters through the unit
`N ≅ f_{T, *}f_T^*N` of `AlgebraicGeometry.Space.modulePushforwardUnitIso`.

**The disjoint union.**  A morphism `h : T ⟶ B` is a morphism from the algebraic space
`(schemeSpaceFunctor B S hS).obj T` to the base, and `CostructuredArrow.mk h` is the
corresponding test scheme over the base, so `X ×_{B, h} T` is `s.baseChange (mk h)`.  The
objects of the fibre over `T` are exactly the objects of `Picardstack_{X/B, σ}` whose test
scheme has underlying scheme `T`, so their structure morphisms range over all such `h`.

**The two coherence inputs.**  The category `Picardstack_{X/B, σ}` is built from a
pseudofunctoriality `hc` of the inverse images (Stacks 03LU) and the coherence `ht` of the
restriction along the section.  The statements here hold for every choice of both, and the
registered statement takes the unconditional terms
`AlgebraicGeometry.Space.modulePushforwardCoherence` and
`AlgebraicGeometry.Space.sectionTransportCoherence`.

**Elaboration.**  The objects of `Picardstack_{X/B}` carry modules whose types mention the base
morphism, so a morphism built by the anonymous constructor has projections that are only
definitionally equal to the data it was built from; comparing composites across that gap is
very expensive.  The lemmas here therefore take the base and the comparison of modules as
separate variables, joined to the morphism by equations
(`AlgebraicGeometry.Space.PicardSituation.transportTrivialization_eq_of_comp_eq`), and destructure
a morphism only after the needed equation has been stated in terms of its projections.

## References

* [Stacks Project, Tag 0D2B](https://stacks.math.columbia.edu/tag/0D2B)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D29](https://stacks.math.columbia.edu/tag/0D29)
* [Stacks Project, Tag 04SA](https://stacks.math.columbia.edu/tag/04SA)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace PicardSituation

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}

/-! ### Rigidity of morphisms compatible with a trivialisation -/

/-- **The part of a transported trivialisation that does not see the comparison of modules**:
for a morphism `b : T ⟶ T'` of test schemes and a trivialisation `α` of `L'` along `σ_{T'}`, the
isomorphism `𝒪_T ≅ b^*𝒪_{T'} ≅ b^*σ_{T'}^*L' ≅ σ_T^*(X_b)^*L'`. -/
def transportPrefix {A C : PicardObject s} (b : A.T ⟶ C.T)
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle) :
    structureModule (s.baseSpaceAt A.T) ≅
      (sectionPullback σ hσ A.T).obj ((modulePullback B S hS (baseChangeMap s.f b)).obj
        C.lineBundle) :=
  structureModulePullbackIso ((schemeSpaceFunctor B S hS).map b.left) ≪≫
    (modulePullback B S hS ((schemeSpaceFunctor B S hS).map b.left)).mapIso α ≪≫
    ((sectionSquareIso σ hσ b).app C.lineBundle).symm

/-- A transported trivialisation is the prefix of its base followed by the restriction along the
section of the comparison of modules. -/
theorem transportTrivialization_eq {A C : PicardObject s} (m : PicardHom A C)
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle) :
    transportTrivialization (σ := σ) (hσ := hσ) m α.hom =
      (transportPrefix m.base α).hom ≫ (sectionPullback σ hσ A.T).map m.fibre := by
  simp only [transportTrivialization, transportPrefix, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]

/-- **Rigidity of a comparison of modules along the section**: when
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism, two comparisons `(X_b)^*L' ⟶ L` along the same base
`b` which transport a trivialisation of `L'` to the same trivialisation of `L` are equal. -/
theorem fibre_eq_of_transportPrefix_comp_eq {A C : PicardObject s}
    (hA : IsIso (s.structureSheafMap A.T)) (b : A.T ⟶ C.T)
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle)
    (φ ψ : (modulePullback B S hS (baseChangeMap s.f b)).obj C.lineBundle ⟶ A.lineBundle)
    (hφ : IsIso φ)
    (h : (transportPrefix b α).hom ≫ (sectionPullback σ hσ A.T).map φ =
      (transportPrefix b α).hom ≫ (sectionPullback σ hσ A.T).map ψ) :
    φ = ψ :=
  (bijective_sectionPullback_map σ hσ hA (modulePullbackInvertible _ _ C.invertible)
    (@asIso _ _ _ _ φ hφ)).1 ((Iso.cancel_iso_hom_left _ _ _).1 h)

/-- `AlgebraicGeometry.Space.PicardSituation.fibre_eq_of_transportPrefix_comp_eq` along two equal
bases. -/
theorem eqToHom_comp_eq_of_transportPrefix_comp_eq {A C : PicardObject s}
    (hA : IsIso (s.structureSheafMap A.T))
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle)
    {b₁ b₂ : A.T ⟶ C.T} (hb : b₁ = b₂)
    (φ : (modulePullback B S hS (baseChangeMap s.f b₁)).obj C.lineBundle ⟶ A.lineBundle)
    (ψ : (modulePullback B S hS (baseChangeMap s.f b₂)).obj C.lineBundle ⟶ A.lineBundle)
    (hφ : IsIso φ)
    (h : (transportPrefix b₁ α).hom ≫ (sectionPullback σ hσ A.T).map φ =
      (transportPrefix b₂ α).hom ≫ (sectionPullback σ hσ A.T).map ψ) :
    eqToHom (by rw [hb]) ≫ φ = ψ := by
  subst hb
  rw [eqToHom_refl, Category.id_comp]
  exact fibre_eq_of_transportPrefix_comp_eq hA _ α φ ψ hφ h

/-- **Computing a transported trivialisation from its base and comparison of modules**: if a
morphism of `Picardstack_{X/B}` has base `b` and comparison `φ`, the trivialisation it transports
is the prefix of `b` followed by the restriction of `φ` along the section. -/
theorem transportTrivialization_eq_of_comp_eq {A C : PicardObject s}
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle)
    (m : PicardHom A C) {b : A.T ⟶ C.T} (hb : m.base = b)
    {φ : (modulePullback B S hS (baseChangeMap s.f b)).obj C.lineBundle ⟶ A.lineBundle}
    (hm : HEq m.fibre φ)
    {β : structureModule (s.baseSpaceAt A.T) ⟶ (sectionPullback σ hσ A.T).obj A.lineBundle}
    (h : (transportPrefix b α).hom ≫ (sectionPullback σ hσ A.T).map φ = β) :
    transportTrivialization (σ := σ) (hσ := hσ) m α.hom = β := by
  subst hb
  obtain rfl := eq_of_heq hm
  exact (transportTrivialization_eq m α).trans h

/-- **A morphism of `Picardstack_{X/B}` is determined by its base and the trivialisation it
transports**, when `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism at the source: two morphisms with
the same base map which transport a trivialisation of the target to the same trivialisation of
the source are equal.  Their comparisons of modules differ by an automorphism whose restriction
along the section is the identity, and restriction along the section is injective. -/
theorem picardHom_eq_of_transportTrivialization_eq {A C : PicardObject s}
    (hA : IsIso (s.structureSheafMap A.T))
    (α : structureModule (s.baseSpaceAt C.T) ≅ (sectionPullback σ hσ C.T).obj C.lineBundle)
    {m n : PicardHom A C} (hb : m.base = n.base)
    (h : transportTrivialization (σ := σ) (hσ := hσ) m α.hom =
      transportTrivialization (σ := σ) (hσ := hσ) n α.hom) :
    m = n := by
  have hf := eqToHom_comp_eq_of_transportPrefix_comp_eq hA α hb m.fibre n.fibre m.isIso_fibre
    ((transportTrivialization_eq m α).symm.trans (h.trans (transportTrivialization_eq n α)))
  obtain ⟨b₁, φ, hφ⟩ := m
  obtain ⟨b₂, ψ, hψ⟩ := n
  obtain rfl : b₁ = b₂ := hb
  obtain rfl : φ = ψ := by simpa using hf
  rfl

/-- **Renormalising a morphism of `Picardstack_{X/B}`.**  When `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism at the source, every morphism `b` of test schemes along which the invertible modules
of two objects of `Picardstack_{X/B, σ}` are isomorphic underlies a morphism of
`Picardstack_{X/B, σ}`: the isomorphism of modules can be rescaled so as to carry the one
trivialisation to the other. -/
theorem exists_sectionedPicardHom {A C : SectionedPicardObject σ hσ}
    (hA : IsIso (s.structureSheafMap A.toPicardObject.T))
    (b : A.toPicardObject.T ⟶ C.toPicardObject.T)
    (e : (modulePullback B S hS (baseChangeMap s.f b)).obj C.toPicardObject.lineBundle ≅
      A.toPicardObject.lineBundle) :
    ∃ m : SectionedPicardHom A C, m.toPicardHom.base = b := by
  have hP := modulePullbackInvertible (baseChangeMap s.f b) _ C.toPicardObject.invertible
  let P := transportPrefix (A := A.toPicardObject) (C := C.toPicardObject) b C.trivialization
  obtain ⟨φ, hφ⟩ := Functor.exists_mapIso_eq (sectionPullback σ hσ A.toPicardObject.T)
    (bijective_sectionPullback_map σ hσ hA hP e).2
    (bijective_sectionPullback_map σ hσ hA A.toPicardObject.invertible e.symm).2
    (bijective_sectionPullback_map σ hσ hA hP (Iso.refl _)).1
    (bijective_sectionPullback_map σ hσ hA A.toPicardObject.invertible (Iso.refl _)).1
    (P.symm ≪≫ A.trivialization)
  have key : P.hom ≫ (sectionPullback σ hσ A.toPicardObject.T).map φ.hom =
      A.trivialization.hom := by
    rw [← Functor.mapIso_hom, hφ, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  let m : PicardHom A.toPicardObject C.toPicardObject := ⟨b, φ.hom, Iso.isIso_hom φ⟩
  exact ⟨⟨m, transportTrivialization_eq_of_comp_eq C.trivialization m (b := b) rfl (φ := φ.hom)
    HEq.rfl key⟩, rfl⟩

/-- The class of the invertible module of the source of a morphism of `Picardstack_{X/B}` is the
pullback of the class of the target along the base. -/
theorem picardClass_eq_picardMap {A C : PicardObject s} (m : PicardHom A C) :
    picardClass _ A.lineBundle A.invertible =
      s.picardMap m.base (picardClass _ C.lineBundle C.invertible) := by
  rw [picardMap_eq, picardPullback_picardClass]
  exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨(asIso m.fibre).symm⟩

/-! ### The object attached to an element of the kernel -/

/-- **The object of `Picardstack_{X/B, σ}` attached to an element of `Ker(σ_T^*)`.**  For a
morphism `h : T ⟶ B` and a class `x` of `Pic(X ×_{B, h} T)` killed by `σ_T^*`, the quadruple
`(T, h, L, α)` with `L` a chosen invertible module of class `x` and `α` a chosen trivialisation
of `L` along `σ_T`, which exists because `σ_T^*[L] = 0`. -/
def kernelObject {U : BigFppfOver B S hS} (h : (schemeSpaceFunctor B S hS).obj U ⟶ s.base)
    (x : {x : s.picardAt (CostructuredArrow.mk h) // sectionPicardPullback σ hσ _ x = 0}) :
    SectionedPicardObject σ hσ where
  toPicardObject :=
    { T := CostructuredArrow.mk h
      lineBundle := (exists_picardClass _ x.1).choose
      invertible := (exists_picardClass _ x.1).choose_spec.choose }
  trivialization :=
    ((sectionPicardPullback_picardClass_eq_zero_iff σ hσ _ _ _).1
      (((exists_picardClass _ x.1).choose_spec.choose_spec).symm ▸ x.2)).some.symm

/-- The object attached to an element of the kernel lies over the morphism `h` it came from. -/
@[simp]
theorem kernelObject_testScheme {U : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ s.base)
    (x : {x : s.picardAt (CostructuredArrow.mk h) // sectionPicardPullback σ hσ _ x = 0}) :
    (kernelObject h x).testScheme = CostructuredArrow.mk h :=
  rfl

/-- The invertible module of the object attached to an element of the kernel has that class. -/
theorem picardClass_kernelObject {U : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ s.base)
    (x : {x : s.picardAt (CostructuredArrow.mk h) // sectionPicardPullback σ hσ _ x = 0}) :
    picardClass _ (kernelObject h x).toPicardObject.lineBundle
      (kernelObject h x).toPicardObject.invertible = x.1 :=
  (exists_picardClass _ x.1).choose_spec.choose_spec

end PicardSituation

/-! ### Fibred in setoids -/

section Sectioned

open PicardSituation

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}
  (hc : ModulePushforwardCoherence B S hS) (ht : SectionTransportCoherence hc σ hσ)

/-- A morphism of the fibre of `Picardstack_{X/B, σ}` over `U` has base morphism the identity
of `U`. -/
theorem sectionedPicardFiberHom_base_left {U : BigFppfOver B S hS}
    {x y : (sectionedPicardCFG hc ht).val.p.Fiber U} (φ : x ⟶ y) :
    (φ.1 : SectionedPicardHom x.1 y.1).toPicardHom.base.left =
      eqToHom x.2 ≫ eqToHom y.2.symm := by
  have := φ.2
  have h := IsHomLift.fac' (sectionedPicardCFG hc ht).val.p (𝟙 U) φ.1
  rwa [Category.id_comp] at h

/-- **The fibres of `Picardstack_{X/B, σ}` are thin** when `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every `T`: between two objects lying over the same scheme there is at most one
morphism over the identity. -/
theorem sectionedPicardFiber_isThin (hstr : s.StructureSheafMapIso) (U : BigFppfOver B S hS) :
    Quiver.IsThin ((sectionedPicardCFG hc ht).val.p.Fiber U) := by
  intro x y
  refine ⟨fun φ ψ ↦ Functor.Fiber.hom_ext (SectionedPicardHom.ext ?_)⟩
  refine picardHom_eq_of_transportTrivialization_eq (hstr _) y.1.trivialization ?_ ?_
  · exact CostructuredArrow.hom_ext _ _ ((sectionedPicardFiberHom_base_left hc ht φ).trans
      (sectionedPicardFiberHom_base_left hc ht ψ).symm)
  · exact ((φ.1 : SectionedPicardHom x.1 y.1).compatible).trans
      ((ψ.1 : SectionedPicardHom x.1 y.1).compatible).symm

/-- **`Picardstack_{X/B, σ}` is fibred in setoids** over the big fppf site of `S` when
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T` over the base. -/
theorem sectionedPicardProjection_isFiberedInSetoids (hstr : s.StructureSheafMapIso) :
    (sectionedPicardCFG hc ht).val.p.IsFiberedInSetoids where
  isFiberedInGroupoids := sectionedPicardProjection_isFiberedInGroupoids hc ht
  fiber_isThin := sectionedPicardFiber_isThin hc ht hstr

/-! ### The isomorphism classes over a scheme -/

/-- **The coproduct `∐_{h : T ⟶ B} Ker(σ_T^* : Pic(X ×_{B, h} T) ⟶ Pic(T))` of Stacks 0D2B**,
over a scheme `U` of the site: pairs of a morphism `h` from `U` to the base and a Picard class of
the base change along `h` killed by restriction along the section. -/
abbrev SectionKernelCoproduct (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (U : BigFppfOver B S hS) :=
  Σ h : (schemeSpaceFunctor B S hS).obj U ⟶ s.base,
    {x : s.picardAt (CostructuredArrow.mk h) // sectionPicardPullback σ hσ _ x = 0}

/-- The map from the coproduct to the isomorphism classes of the fibre over `U`: an element
`(h, [L])` goes to the class of the object `(U, h, L, α)` for a chosen trivialisation `α`. -/
def kernelCoproductToIsoClass (U : BigFppfOver B S hS)
    (c : SectionKernelCoproduct σ hσ U) :
    Quotient (isIsomorphicSetoid ((sectionedPicardCFG hc ht).val.p.Fiber U)) :=
  Quotient.mk _ ⟨kernelObject c.1 c.2, rfl⟩

/-- A morphism of `Picardstack_{X/B, σ}` between objects of the fibre over `U` whose base has the
identity of `U` as underlying morphism of schemes gives an isomorphism of the fibre. -/
theorem nonempty_fiber_iso_of_sectionedPicardHom {U : BigFppfOver B S hS}
    (x y : (sectionedPicardCFG hc ht).val.p.Fiber U) (m : SectionedPicardHom x.1 y.1)
    (hm : m.toPicardHom.base.left = eqToHom x.2 ≫ eqToHom y.2.symm) :
    Nonempty (x ≅ y) := by
  have : (sectionedPicardCFG hc ht).val.p.IsHomLift (𝟙 U) (m : x.1 ⟶ y.1) :=
    IsHomLift.of_fac' _ _ _ x.2 y.2 (by rwa [Category.id_comp])
  have hg := (sectionedPicardProjection_isFiberedInGroupoids hc ht).fiber_isGroupoid U
  let f : x ⟶ y := Functor.Fiber.homMk _ U (m : x.1 ⟶ y.1)
  exact ⟨@asIso _ _ _ _ f (hg.all_isIso f)⟩

/-- **Every object of the fibre over its scheme is isomorphic to the object attached to its
class.**  For an object `(T, h, L, α)` of `Picardstack_{X/B, σ}`, the object attached to
`(h, [L])` is isomorphic to it in the fibre over `T`: both have invertible modules of class
`[L]`, and their trivialisations can be matched because `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism. -/
theorem kernelCoproductToIsoClass_picardClass (hstr : s.StructureSheafMapIso)
    (A : SectionedPicardObject σ hσ) :
    kernelCoproductToIsoClass hc ht A.testScheme.left
        ⟨A.testScheme.hom, ⟨picardClass _ A.toPicardObject.lineBundle
          A.toPicardObject.invertible,
          (sectionPicardPullback_picardClass_eq_zero_iff σ hσ A.testScheme _ _).2
            ⟨A.trivialization.symm⟩⟩⟩ =
      Quotient.mk _ ⟨A, rfl⟩ := by
  let x : {x : s.picardAt (CostructuredArrow.mk A.testScheme.hom) //
      sectionPicardPullback σ hσ _ x = 0} :=
    ⟨picardClass _ A.toPicardObject.lineBundle A.toPicardObject.invertible,
      (sectionPicardPullback_picardClass_eq_zero_iff σ hσ A.testScheme _ _).2
        ⟨A.trivialization.symm⟩⟩
  let K := kernelObject (σ := σ) (hσ := hσ) A.testScheme.hom x
  obtain ⟨e⟩ := (picardClass_eq_picardClass_iff _ _ _ _ _).1
    (picardClass_kernelObject (σ := σ) (hσ := hσ) A.testScheme.hom x)
  obtain ⟨m, hm⟩ := exists_sectionedPicardHom (A := K) (C := A) (hstr _) (𝟙 A.testScheme)
    ((baseChangeIdComparison hc s.f A.testScheme).app A.toPicardObject.lineBundle ≪≫ e.symm)
  refine Quotient.sound (nonempty_fiber_iso_of_sectionedPicardHom hc ht ⟨K, rfl⟩ ⟨A, rfl⟩ m ?_)
  rw [hm]
  simp only [CostructuredArrow.id_left, eqToHom_trans]
  exact (eqToHom_refl _ _).symm

/-- **Objects with the same image in the coproduct are isomorphic**, and conversely the map
from the coproduct to the isomorphism classes is injective: an isomorphism over the identity of
`U` between the objects attached to `(h, [L])` and `(h', [L'])` forces `h = h'`, and then its
base is the identity, so `[L] = [L']`. -/
theorem kernelCoproductToIsoClass_injective (U : BigFppfOver B S hS) :
    Function.Injective (kernelCoproductToIsoClass (σ := σ) (hσ := hσ) hc ht U) := by
  rintro ⟨h, x⟩ ⟨h', x'⟩ hxy
  obtain ⟨e⟩ := Quotient.exact hxy
  let m : SectionedPicardHom (kernelObject h x) (kernelObject h' x') := e.hom.1
  have hl : m.toPicardHom.base.left = 𝟙 U :=
    (sectionedPicardFiberHom_base_left hc ht e.hom).trans
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
  have hw : h' = h := by simpa [hl] using CostructuredArrow.w m.toPicardHom.base
  subst hw
  have hb : m.toPicardHom.base = 𝟙 _ := CostructuredArrow.hom_ext _ _ hl
  have hcl := picardClass_eq_picardMap m.toPicardHom
  rw [hb] at hcl
  have hxx : x.1 = x'.1 := (picardClass_kernelObject h' x).symm.trans
    (hcl.trans ((s.picardMap_id hc _ _).trans (picardClass_kernelObject h' x')))
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxx))

/-- The map from the coproduct to the isomorphism classes of the fibre over `U` is surjective:
every object of the fibre is isomorphic to the object attached to its class. -/
theorem kernelCoproductToIsoClass_surjective (hstr : s.StructureSheafMapIso)
    (U : BigFppfOver B S hS) :
    Function.Surjective (kernelCoproductToIsoClass (σ := σ) (hσ := hσ) hc ht U) := by
  intro q
  induction q using Quotient.inductionOn with
  | h y =>
    obtain ⟨A, hA⟩ := y
    subst hA
    exact ⟨_, kernelCoproductToIsoClass_picardClass hc ht hstr A⟩

/-- **The bijection of Stacks 0D2B.**  When `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every
`T`, the isomorphism classes of the fibre of `Picardstack_{X/B, σ}` over a scheme `U` correspond
to `∐_{h : U ⟶ B} Ker(σ_U^* : Pic(X ×_{B, h} U) ⟶ Pic(U))`; the class of `(U, h, L, α)` goes to
`(h, [L])` (`AlgebraicGeometry.Space.sectionedPicardIsoClassEquiv_mk`). -/
def sectionedPicardIsoClassEquiv (hstr : s.StructureSheafMapIso) (U : BigFppfOver B S hS) :
    Quotient (isIsomorphicSetoid ((sectionedPicardCFG hc ht).val.p.Fiber U)) ≃
      SectionKernelCoproduct σ hσ U :=
  (Equiv.ofBijective _ ⟨kernelCoproductToIsoClass_injective hc ht U,
    kernelCoproductToIsoClass_surjective hc ht hstr U⟩).symm

/-- **The bijection of Stacks 0D2B sends the class of `(T, h, L, α)` to `(h, [L])`.** -/
theorem sectionedPicardIsoClassEquiv_mk (hstr : s.StructureSheafMapIso)
    (A : SectionedPicardObject σ hσ) :
    sectionedPicardIsoClassEquiv hc ht hstr A.testScheme.left (Quotient.mk _ ⟨A, rfl⟩) =
      ⟨A.testScheme.hom, ⟨picardClass _ A.toPicardObject.lineBundle
        A.toPicardObject.invertible,
        (sectionPicardPullback_picardClass_eq_zero_iff σ hσ A.testScheme _ _).2
          ⟨A.trivialization.symm⟩⟩⟩ := by
  rw [sectionedPicardIsoClassEquiv, Equiv.symm_apply_eq]
  exact (kernelCoproductToIsoClass_picardClass hc ht hstr A).symm

/-- Both conclusions of Stacks 0D2B for the category `Picardstack_{X/B, σ}` built from any
pseudofunctoriality datum `hc` of Stacks 03LU and any coherence `ht` of the restriction along the
section; `AlgebraicGeometry.Space.sectionedPicardCFG_isFiberedInSetoids_and_isoClassEquiv` is
the instance at the canonical data. -/
theorem sectionedPicardCFG_isFiberedInSetoids_and_isoClassEquiv_of_coherence
    (hstr : s.StructureSheafMapIso) :
    (sectionedPicardCFG hc ht).val.p.IsFiberedInSetoids ∧
      ∀ A : SectionedPicardObject σ hσ,
        sectionedPicardIsoClassEquiv hc ht hstr A.testScheme.left (Quotient.mk _ ⟨A, rfl⟩) =
          ⟨A.testScheme.hom, ⟨picardClass _ A.toPicardObject.lineBundle
            A.toPicardObject.invertible,
            (sectionPicardPullback_picardClass_eq_zero_iff σ hσ A.testScheme _ _).2
              ⟨A.trivialization.symm⟩⟩⟩ :=
  ⟨sectionedPicardProjection_isFiberedInSetoids hc ht hstr,
    sectionedPicardIsoClassEquiv_mk hc ht hstr⟩

end Sectioned

/-- In Situation 0D25, let `σ` be a section of `f : X ⟶ B` and assume that
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T` over `B`.  Then
`Picardstack_{X/B, σ} ⟶ (Sch/S)_{fppf}` is fibred in setoids, and its set of isomorphism classes
over a scheme `T` is `∐_{h : T ⟶ B} Ker(σ_T^* : Pic(X ×_{B, h} T) ⟶ Pic(T))`, through the
bijection `AlgebraicGeometry.Space.sectionedPicardIsoClassEquiv` sending the class of
`(T, h, L, α)` to `(h, [L])`.

`Picardstack_{X/B, σ}` is `AlgebraicGeometry.Space.sectionedPicardCFG` at the pseudofunctoriality
`AlgebraicGeometry.Space.modulePushforwardCoherence` of Stacks 03LU and the coherence
`AlgebraicGeometry.Space.sectionTransportCoherence` of the restriction along the section, both
unconditional. -/
@[stacks 0D2B]
theorem sectionedPicardCFG_isFiberedInSetoids_and_isoClassEquiv {s : PicardSituation B S hS}
    (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (hstr : s.StructureSheafMapIso) :
    (sectionedPicardCFG (modulePushforwardCoherence B S hS)
        (sectionTransportCoherence _ σ hσ)).val.p.IsFiberedInSetoids ∧
      ∀ A : PicardSituation.SectionedPicardObject σ hσ,
        sectionedPicardIsoClassEquiv (modulePushforwardCoherence B S hS)
            (sectionTransportCoherence _ σ hσ) hstr A.testScheme.left
            (Quotient.mk _ ⟨A, rfl⟩) =
          ⟨A.testScheme.hom, ⟨picardClass _ A.toPicardObject.lineBundle
            A.toPicardObject.invertible,
            (PicardSituation.sectionPicardPullback_picardClass_eq_zero_iff σ hσ A.testScheme
              _ _).2 ⟨A.trivialization.symm⟩⟩⟩ :=
  sectionedPicardCFG_isFiberedInSetoids_and_isoClassEquiv_of_coherence _ _ hstr

end AlgebraicGeometry.Space

end
