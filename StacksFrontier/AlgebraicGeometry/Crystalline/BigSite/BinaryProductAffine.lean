module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Colimit
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineSections

/-!
# Products of pairs in the big crystalline category, affine case

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p` nilpotent
on `Γ(X, ⊤)`.  This file proves that two objects of `CRIS(X/S)` whose thickened schemes are affine
have a product in `CRIS(X/S)`.  It is the affine half of [Stacks, Tag 07I9], and it is the step the
tag reduces to: the ambient scheme of an affine object is affine, so taking global sections turns
the product into the coproduct of [Stacks, Tag 07HN] in the ring-theoretic crystalline category
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` of [Stacks, Tag 07HM].

The product is produced by three ingredients that are already in the library, plus one that is
built here.  Already available: the affine-to-global bridge
`Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine` is fully faithful on the objects
with affine thickened scheme (`wholeHomToAffine_bijective`); the coproduct in
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))` exists (`Crystalline.binaryCoproductWithTensorProductQuotient`); and an
object of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` is realised in `CRIS(X/S)` by
`Crystalline.GlobalCrystallineSituation.specThickeningOfAffine`, whose thickened scheme
`Spec (B/J)` is affine.  Built here: the **universal property against an arbitrary object `T` of
`CRIS(X/S)`**, whose thickened scheme need not be affine, so that `wholeThickeningToAffine` does
not apply to it.  The replacement is a divided power thickening of global sections attached to `T`
*relative to* a morphism `f : T ⟶ A` into an affine object,
`Crystalline.GlobalCrystallineSituation.relativeSections`: the structural map
`Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` cannot be built from `T` alone and is obtained through `f`.

What makes the relative construction work is that `Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)` is **injective**
for every divided power thickening of schemes, affine or not
(`Crystalline.SchemeThickening.sourceQuotientHom_injective`); it is surjectivity that needs
affineness.  Injectivity is the statement that the divided power ideal of global sections is
exactly the kernel of restriction to the thickened scheme, which holds over an arbitrary open
because membership in a submodule of a sheaf of modules is a local condition.

## Main definitions

* `Crystalline.SchemeThickening.sourceQuotientHom` — restriction to the thickened scheme, read on
  the quotient of the global sections of the ambient scheme by the divided power ideal, for an
  **arbitrary** divided power thickening of schemes.
* `Crystalline.GlobalCrystallineSituation.specThickeningSectionsIso` — the comparison isomorphism
  identifying the global sections of `Spec (B, J, δ)` with `(B, J, δ)`, with no hypothesis on the
  thickened scheme of the realisation.
* `Crystalline.GlobalCrystallineSituation.relativeSections` — **the divided power thickening of
  global sections of an arbitrary object `T` of `CRIS(X/S)`, relative to a morphism from `T` to an
  object with affine thickened scheme.**
* `Crystalline.GlobalCrystallineSituation.relativeSectionsMap` and
  `Crystalline.GlobalCrystallineSituation.homOfRelativeSections` — the two directions of the
  resulting bijection between morphisms `T ⟶ B` of `CRIS(X/S)` into an affine object and
  morphisms `Γ(B, ⊤) ⟶ relativeSections f` of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`.
* `Crystalline.GlobalCrystallineSituation.liftOfIsColimit` — the morphism into the realisation of
  the coproduct induced by a cone with arbitrary vertex, and
  `Crystalline.GlobalCrystallineSituation.isLimitBinaryFanOfIsColimit`, the resulting limit fan.

## Main results

* `Crystalline.SchemeThickening.sectionsIdeal_eq_ker_appTop` — the divided power ideal of global
  sections of a divided power thickening of schemes is the kernel of restriction to the thickened
  scheme, with **no affineness hypothesis**.
* `Crystalline.GlobalCrystallineSituation.relativeSectionsMap_injective` and
  `Crystalline.GlobalCrystallineSituation.relativeSectionsMap_homOfRelativeSections` — the
  bijection above.
* **`Crystalline.GlobalCrystallineSituation.hasBinaryProduct_of_isAffine`** — two objects of
  `CRIS(X/S)` with affine thickened schemes have a product.

## What is and is not proved

No tag attribute is placed in this file.  **This is not [Stacks, Tag 07I9]**: the tag asserts that
`CRIS(X/S)` has all nonempty finite limits for an arbitrary global crystalline situation, and what
is proved here is the existence of products of *pairs* of objects with *affine* thickened scheme,
over a situation with `X` and `S` affine.  Three further steps separate the two:

1. fibre products, which the library has for `CRIS(X/S)` in
   `StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/FibreProduct.lean` and which are not
   touched here;
2. the passage from affine objects to arbitrary ones, which needs the descent of a divided power
   thickening along an open cover of the thickened scheme — absent from the library for
   `Crystalline.SchemeThickening`, see the module docstring of
   `StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/AffineSections.lean`;
3. the passage from an affine situation to an arbitrary one, which is the restriction of the
   situation to a pair of opens of
   `StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/SituationRestrict.lean` together with the
   same descent.

The hypothesis `hp` is not derived: a `GlobalCrystallineSituation` asks `p` to be nilpotent in
every local ring of `X`, which for affine `X` gives nilpotence in `Γ(X, ⊤)` but by an implication
the library does not have; see `Crystalline.GlobalCrystallineSituation.affineSituation`.

## References

* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-- **Membership in a submodule of a sheaf of modules on a scheme is local on affine opens.**  A
section over an open `V` whose restriction to every affine open contained in `V` lies in the
submodule lies in the submodule over `V`, because the affine opens contained in `V` cover it and
the membership condition of a `SheafOfModules.Submodule` is local. -/
theorem mem_of_mem_affineOpens {X : Scheme.{u}}
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule) (V : X.Opens) (s : Γ(X, V))
    (h : ∀ (A : X.affineOpens) (hAV : (A : X.Opens) ≤ V),
      (X.presheaf.map (homOfLE hAV).op).hom s ∈ I.obj (op (A : X.Opens))) :
    s ∈ I.obj (op V) := by
  let R : Presieve V := fun W _ ↦ ∃ A : X.affineOpens, W = (A : X.Opens) ∧ (A : X.Opens) ≤ V
  have hcov : Sieve.generate R ∈ Opens.grothendieckTopology X V := by
    intro x hx
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact ⟨A, homOfLE hAV, ⟨A, 𝟙 _, homOfLE hAV, ⟨⟨A, hA⟩, rfl, hAV⟩, by simp⟩, hxA⟩
  have hR : R ≤ I.toSubmodule.toSubfunctor.sieveOfSection s := by
    rintro W f ⟨A, rfl, hAV⟩
    exact h A hAV
  exact I.isSheaf s ((Opens.grothendieckTopology X).superset_covering
    ((Sieve.generate_le_iff R _).2 hR) hcov)

namespace SchemeThickening

variable (D : SchemeThickening.{u})

/-- **Every global section of the divided power ideal of a divided power thickening of schemes
dies on the thickened scheme.**  The thickened scheme is the closed fibre of the ambient divided
power scheme (`Crystalline.SchemeThickening.closedFiberSourceIso`), and a section of the divided
power ideal over an arbitrary open dies on the closed fibre.  No affineness is needed. -/
theorem sectionsIdeal_le_ker_appTop :
    sectionsIdeal D ≤ RingHom.ker D.immersion.appTop.hom := by
  intro s hs
  rw [RingHom.mem_ker]
  have h0 : (DividedPowerScheme.closedFiberι D.target).appTop.hom s = 0 :=
    (DividedPowerScheme.closedFiberPresentation D.target).app_eq_zero_of_mem ⊤ s hs
  have h := congrArg Scheme.Hom.appTop D.closedFiberSourceIso_inv_closedFiberι
  rw [Scheme.Hom.comp_appTop] at h
  refine (ConcreteCategory.congr_hom h s).symm.trans ?_
  change D.closedFiberSourceIso.inv.appTop.hom
    ((DividedPowerScheme.closedFiberι D.target).appTop.hom s) = 0
  rw [h0, map_zero]

/-- **A global section of the ambient scheme of a divided power thickening of schemes that dies on
the thickened scheme lies in the divided power ideal.**  On an affine open the two agree, by the
defining condition `Crystalline.SchemeThickening.ideal_eq_ker` and
`AlgebraicGeometry.Scheme.Hom.ker_apply`; the passage to `⊤` is
`Crystalline.mem_of_mem_affineOpens`, the locality of membership in the divided power ideal.  No
affineness is needed. -/
theorem ker_appTop_le_sectionsIdeal :
    RingHom.ker D.immersion.appTop.hom ≤ sectionsIdeal D := by
  intro s hs
  refine mem_of_mem_affineOpens D.target.ideal ⊤ s fun A hA ↦ ?_
  have hnat := ConcreteCategory.congr_hom
    (D.immersion.naturality (homOfLE hA).op (U := (A : D.target.scheme.Opens)) (U' := ⊤)) s
  have hmem : (D.target.scheme.presheaf.map (homOfLE hA).op).hom s ∈
      RingHom.ker (D.immersion.app (A : D.target.scheme.Opens)).hom := by
    rw [RingHom.mem_ker]
    refine hnat.trans ?_
    change (D.source.presheaf.map _).hom (D.immersion.appTop.hom s) = 0
    rw [RingHom.mem_ker.mp hs, map_zero]
  exact ((D.ideal_eq_ker A).trans (Scheme.Hom.ker_apply D.immersion A)).ge hmem

/-- **For an arbitrary divided power thickening of schemes, the divided power ideal of global
sections is exactly the kernel of restriction to the thickened scheme.**  This strengthens
`Crystalline.SchemeThickening.sectionsIdeal_eq_ker`, which assumes the thickened scheme affine;
affineness is what makes the restriction *surjective*, not what identifies its kernel. -/
theorem sectionsIdeal_eq_ker_appTop :
    sectionsIdeal D = RingHom.ker D.immersion.appTop.hom :=
  le_antisymm D.sectionsIdeal_le_ker_appTop D.ker_appTop_le_sectionsIdeal

/-- **Restriction to the thickened scheme, read on the quotient of the global sections of the
ambient scheme by the divided power ideal**, for an arbitrary divided power thickening of schemes.
For an affine thickened scheme this is `Crystalline.SchemeThickening.sectionsQuotientHom`, which is
moreover bijective. -/
def sourceQuotientHom : (↑Γ(D.target.scheme, ⊤) ⧸ sectionsIdeal D) →+* Γ(D.source, ⊤) :=
  Ideal.Quotient.lift _ D.immersion.appTop.hom fun _ ha ↦
    RingHom.mem_ker.mp (D.sectionsIdeal_le_ker_appTop ha)

/-- Restriction on the quotient sends the class of a global section `x` of the ambient scheme to
the restriction of `x` to the thickened scheme. -/
@[simp]
theorem sourceQuotientHom_mk (x : ↑Γ(D.target.scheme, ⊤)) :
    D.sourceQuotientHom (Ideal.Quotient.mk (sectionsIdeal D) x) =
      D.immersion.appTop.hom x := rfl

/-- For an affine thickened scheme, restriction on the quotient is the restriction isomorphism
`Crystalline.SchemeThickening.sectionsQuotientEquiv`. -/
theorem sourceQuotientHom_eq_sectionsQuotientEquiv [IsAffine D.source]
    (q : ↑Γ(D.target.scheme, ⊤) ⧸ sectionsIdeal D) :
    D.sourceQuotientHom q = D.sectionsQuotientEquiv q := rfl

/-- **The global sections of the ambient scheme of a divided power thickening of schemes, modulo
the divided power ideal, inject into the global sections of the thickened scheme.**  This is the
half of `Crystalline.SchemeThickening.bijective_sectionsQuotientHom` that survives without
affineness, and it is what makes the relative sections construction below well defined. -/
theorem sourceQuotientHom_injective : Function.Injective D.sourceQuotientHom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact D.ker_appTop_le_sectionsIdeal (RingHom.mem_ker.mpr hq)

/-- **Restriction on the quotient is natural in the divided power thickening of schemes**, read on
the class of a global section.  A morphism `t` of ambient divided power schemes together with a
morphism `v` of thickened schemes making the square of immersions commute carries the class of `x`
to the image under `v` of the class of `x`.

The statement is deliberately written with `Ideal.Quotient.mk` and
`Crystalline.SchemeThickening.sectionsIdeal` spelled out on both sides rather than through
`DividedPowerRing.quotientRingHom`: the two spellings of the divided power ideal of global sections
are definitionally but not syntactically equal, so a version phrased through `quotientRingHom` is
not usable by `rw`. -/
theorem sourceQuotientHom_mk_appTop {D E : SchemeThickening.{u}} (t : D.target ⟶ E.target)
    (v : D.source ⟶ E.source) (h : D.immersion ≫ t.hom = v ≫ E.immersion)
    (x : ↑Γ(E.target.scheme, ⊤)) :
    D.sourceQuotientHom (Ideal.Quotient.mk (sectionsIdeal D) (t.hom.appTop.hom x)) =
      v.appTop.hom (E.sourceQuotientHom (Ideal.Quotient.mk (sectionsIdeal E) x)) :=
  Stacks.Thickenings.appTop_comm_of_comm h x

end SchemeThickening

namespace GlobalCrystallineSituation

section Constructions

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

section SpecIso

variable (T : DividedPowerThickening.{u, u, u} (affineSituation S hp))

/-- **The structural maps of `(B, J, δ)` and of the global sections of its realisation correspond
under `Crystalline.DividedPowerScheme.specSectionsRingIso`.**  This is
`Crystalline.GlobalCrystallineSituation.quotientMap_specSectionsRingIso_hom_comp` without the
hypothesis that the thickened scheme of the realisation is the whole of `X`. -/
theorem quotientRingHom_specSectionsRingIso_comp :
    (DividedPowerRing.quotientRingHom (A := T.ring)
        (B := (wholeThickeningToAffine hp (specThickeningOfAffine hp T)).ring)
        (DividedPowerScheme.specSectionsRingIso T.ring).hom).comp T.toQuotient =
      (wholeThickeningToAffine hp (specThickeningOfAffine hp T)).toQuotient := by
  refine RingHom.ext fun y ↦ ?_
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (T.toQuotient y)
  change DividedPowerRing.quotientRingHom (A := T.ring)
    (B := (wholeThickeningToAffine hp (specThickeningOfAffine hp T)).ring)
    (DividedPowerScheme.specSectionsRingIso T.ring).hom (T.toQuotient y) = _
  rw [← hβ]
  refine (DividedPowerRing.quotientRingHom_mk (A := T.ring)
    (B := (wholeThickeningToAffine hp (specThickeningOfAffine hp T)).ring)
    (DividedPowerScheme.specSectionsRingIso T.ring).hom β).trans ?_
  exact (wholeSectionsToQuotient_eq_mk hp T hβ).symm

/-- **The global sections of the object of `CRIS(X/S)` attached to `(B, J, δ)` are `(B, J, δ)`.**
This is `Crystalline.GlobalCrystallineSituation.wholeThickeningToAffineSpecIso` without the
hypothesis `[IsIso (specThickeningOfAffine hp T).toX]`, which is false for the realisation of a
coproduct: the thickened scheme of a product of two objects is not the whole of `X`. -/
def specThickeningSectionsIso :
    wholeThickeningToAffine hp (specThickeningOfAffine hp T) ≅ T :=
  (DividedPowerThickening.isoOfRingIso (X := T)
    (Y := wholeThickeningToAffine hp (specThickeningOfAffine hp T))
    (DividedPowerScheme.specSectionsRingIso T.ring)
    (DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism
      (specFromBase hp T)).symm
    (quotientRingHom_specSectionsRingIso_comp hp T)).symm

end SpecIso

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The structural map of an object with affine thickened scheme, read through restriction to the
thickened scheme, is the restriction `Γ(X, ⊤) → Γ(U, ⊤)`.**  This is
`Crystalline.GlobalCrystallineSituation.sectionsQuotientEquiv_wholeSectionsToQuotient` phrased
through `Crystalline.SchemeThickening.sourceQuotientHom`. -/
theorem sourceQuotientHom_wholeSectionsToQuotient (D : Thickening S)
    [IsAffine D.thickening.source] (x : Γ(S.X, ⊤)) :
    D.thickening.sourceQuotientHom (wholeSectionsToQuotient D x) = D.toX.appTop.hom x :=
  sectionsQuotientEquiv_wholeSectionsToQuotient D x

section Relative

variable {T A B C : Thickening S} [IsAffine A.thickening.source] [IsAffine B.thickening.source]
  [IsAffine C.thickening.source]

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **A morphism of `CRIS(X/S)` into an object with affine thickened scheme is determined by its
effect on the global sections of the ambient schemes.**  The source is arbitrary: the ambient
scheme of the *target* being affine is what pins down the morphism of ambient schemes, and the
morphism of thickened schemes then follows because the immersion of the target is a monomorphism.
This is `Crystalline.GlobalCrystallineSituation.wholeHomToAffine_injective` with the affineness
hypothesis on the source dropped. -/
theorem hom_ext_of_appTop {g g' : T ⟶ B}
    (h : g.targetHom.hom.appTop = g'.targetHom.hom.appTop) : g = g' := by
  have hT : g.targetHom = g'.targetHom := DividedPowerScheme.Hom.ext (ext_of_isAffine h)
  have hS : g.sourceHom = g'.sourceHom := by
    refine (cancel_mono B.thickening.immersion).mp ?_
    rw [← g.immersion_naturality, ← g'.immersion_naturality, hT]
  exact Thickening.Hom.ext hS hT

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **A morphism of ambient divided power schemes over `X` carries the structural map of an object
with affine thickened scheme to the restriction `Γ(X, ⊤) → Γ(U_T, ⊤)`**, read through the injection
`Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)`.  A section of `X` is carried into the thickened scheme of `B` and
lifts along the surjection `Γ(T_B, ⊤) → Γ(U_B, ⊤)`; the square of immersions transports the
identity.

The morphism of divided power rings `φ` is taken as a separate argument together with the equation
identifying it with the one induced by `t` on global sections, so that the statement can be applied
to a `φ` whose type is spelled through a divided power thickening rather than through
`Crystalline.SchemeThickening.sectionsRing`. -/
theorem sourceQuotientHom_quotientRingHom_wholeSectionsToQuotient
    (t : T.thickening.target ⟶ B.thickening.target)
    (v : T.thickening.source ⟶ B.thickening.source)
    (hv : T.thickening.immersion ≫ t.hom = v ≫ B.thickening.immersion)
    (φ : B.thickening.sectionsRing ⟶ T.thickening.sectionsRing)
    (hφ : globalSectionsDPMorphism t = φ) (x : Γ(S.X, ⊤)) :
    T.thickening.sourceQuotientHom
        (DividedPowerRing.quotientRingHom φ (wholeSectionsToQuotient B x)) =
      v.appTop.hom (B.toX.appTop.hom x) := by
  subst hφ
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (wholeSectionsToQuotient B x)
  rw [← hb]
  exact (SchemeThickening.sourceQuotientHom_mk_appTop t v hv b).trans (congrArg _
    ((congrArg B.thickening.sourceQuotientHom hb).trans
      (sourceQuotientHom_wholeSectionsToQuotient B x)))

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **A morphism of `CRIS(X/S)` into an object with affine thickened scheme carries the structural
map of the target to the restriction `Γ(X, ⊤) → Γ(U_T, ⊤)`**, read through the injection
`Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)`. -/
theorem sourceQuotientHom_quotientRingHom_targetHom (g : T ⟶ B) (x : Γ(S.X, ⊤)) :
    T.thickening.sourceQuotientHom
        (DividedPowerRing.quotientRingHom (globalSectionsDPMorphism g.targetHom)
          (wholeSectionsToQuotient B x)) = T.toX.appTop.hom x :=
  (sourceQuotientHom_quotientRingHom_wholeSectionsToQuotient g.targetHom g.sourceHom
      g.immersion_naturality _ rfl x).trans
    (congrArg (fun k : T.thickening.source ⟶ S.X ↦ k.appTop.hom x) g.toX_naturality)

/-- **The divided power thickening of global sections of an arbitrary object `T` of `CRIS(X/S)`,
relative to a morphism `f : T ⟶ A` into an object with affine thickened scheme.**  The divided
power ring is the ring of global sections `(Γ(T, ⊤), I_T(⊤), δ)` of the ambient scheme and the map
from the base is the map on global sections of `T ⟶ S`, exactly as in
`Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine`; what the morphism `f` supplies is
the structural map `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)`, obtained from the structural map of `A` by pushing
it forward along `f`.

For a general `T` the structural map cannot be built from `T` alone: it would be the restriction
`Γ(X, ⊤) → Γ(U_T, ⊤)` read backwards through `Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)`, which is injective by
`Crystalline.SchemeThickening.sourceQuotientHom_injective` but surjective only when `U_T` is
affine. -/
def relativeSections (f : T ⟶ A) :
    DividedPowerThickening.{u, u, u} (affineSituation S hp) where
  ring := T.thickening.sectionsRing
  fromBase := globalSectionsDPMorphism T.toBase
  prime_nilpotent := by
    have h := (isNilpotent_prime_sections hp A).map f.targetHom.hom.appTop.hom
    rwa [map_natCast] at h
  toQuotient := (DividedPowerRing.quotientRingHom
    (globalSectionsDPMorphism f.targetHom)).comp (wholeSectionsToQuotient A)
  commutes := by
    refine RingHom.ext fun x ↦ ?_
    have hA : Ideal.Quotient.mk (SchemeThickening.sectionsIdeal A.thickening)
        (A.toBase.hom.appTop.hom x) =
        wholeSectionsToQuotient A (baseSectionsToSections S x) :=
      DFunLike.congr_fun (wholeSectionsToQuotient_commutes A) x
    have hb : (f.targetHom ≫ A.toBase).hom.appTop.hom x = T.toBase.hom.appTop.hom x :=
      congrArg (fun k : T.thickening.target ⟶ S.S ↦ k.hom.appTop.hom x) f.base_naturality
    exact (congrArg
        (Ideal.Quotient.mk (SchemeThickening.sectionsIdeal T.thickening)) hb.symm).trans
      (congrArg (DividedPowerRing.quotientRingHom (globalSectionsDPMorphism f.targetHom)) hA)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The structural map of the relative sections of `T` is the restriction `Γ(X, ⊤) → Γ(U_T, ⊤)`,
read through the injection `Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)`.**  In particular it does not depend on the
morphism `f` used to build it. -/
theorem sourceQuotientHom_relativeSections_toQuotient (f : T ⟶ A) (x : Γ(S.X, ⊤)) :
    T.thickening.sourceQuotientHom ((relativeSections hp f).toQuotient x) =
      T.toX.appTop.hom x :=
  sourceQuotientHom_quotientRingHom_targetHom f x

/-- **The morphism of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` attached to a morphism `g : T ⟶ B` of `CRIS(X/S)`
into an object with affine thickened scheme**, relative to a morphism `f : T ⟶ A` into another such
object.  It is the map on global sections of the ambient divided power schemes, so the assignment
is contravariant, exactly as for `Crystalline.GlobalCrystallineSituation.wholeHomToAffine`; the
compatibility with the structural maps is where the injectivity of
`Γ(T, ⊤)/I_T(⊤) → Γ(U_T, ⊤)` is used. -/
def relativeSectionsMap (f : T ⟶ A) (g : T ⟶ B) :
    wholeThickeningToAffine hp B ⟶ relativeSections hp f where
  hom := globalSectionsDPMorphism g.targetHom
  fromBase_comp :=
    (globalSectionsDPMorphism_comp g.targetHom B.toBase).trans
      (congrArg (fun h : T.thickening.target ⟶ S.S ↦ globalSectionsDPMorphism h)
        g.base_naturality)
  toQuotient_comp := RingHom.ext fun x ↦ T.thickening.sourceQuotientHom_injective
    ((sourceQuotientHom_quotientRingHom_targetHom g x).trans
      (sourceQuotientHom_relativeSections_toQuotient hp f x).symm)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The underlying morphism of divided power rings of
`Crystalline.GlobalCrystallineSituation.relativeSectionsMap` is the map on global sections of the
ambient divided power schemes. -/
@[simp]
theorem relativeSectionsMap_hom (f : T ⟶ A) (g : T ⟶ B) :
    (relativeSectionsMap hp f g).hom = globalSectionsDPMorphism g.targetHom := rfl

omit [IsAffine S.X] in
/-- **The morphism of ambient divided power schemes realising a morphism of divided power
thickenings of global sections is a morphism over the base.**  The base being affine, this is
checked on global sections, where it is the compatibility `fromBase_comp` of
[Stacks, Tag 07HM]. -/
theorem homOfSectionsDPMorphism_base_naturality (f : T ⟶ A)
    (g : wholeThickeningToAffine hp B ⟶ relativeSections hp f) :
    DividedPowerScheme.homOfSectionsDPMorphism g.hom ≫ B.toBase = T.toBase := by
  refine DividedPowerScheme.Hom.ext
    (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)))
  exact (ConcreteCategory.congr_hom
      (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop g.hom)
      (B.toBase.hom.appTop.hom c)).trans (DFunLike.congr_fun g.fromBase_comp c)

omit [IsAffine S.S.scheme] in
/-- **The induced map on thickened schemes is a morphism over `X`.**  Both maps land in the affine
scheme `X`, so the identity is checked on global sections, where it is the compatibility
`toQuotient_comp` of [Stacks, Tag 07HM] read through
`Crystalline.SchemeThickening.sourceQuotientHom`. -/
theorem homOfSectionsDPMorphism_toX_naturality (f : T ⟶ A)
    (g : wholeThickeningToAffine hp B ⟶ relativeSections hp f) :
    SchemeThickening.sourceMapOfTargetMap
        (DividedPowerScheme.homOfSectionsDPMorphism g.hom) ≫ B.toX = T.toX := by
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  refine (sourceQuotientHom_quotientRingHom_wholeSectionsToQuotient
    (DividedPowerScheme.homOfSectionsDPMorphism g.hom)
    (SchemeThickening.sourceMapOfTargetMap
      (DividedPowerScheme.homOfSectionsDPMorphism g.hom))
    (SchemeThickening.sourceMapOfTargetMap_immersion _) g.hom
    (DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism g.hom) x).symm.trans ?_
  exact (congrArg (fun k : Γ(S.X, ⊤) →+* _ ↦ T.thickening.sourceQuotientHom (k x))
      g.toQuotient_comp).trans (sourceQuotientHom_relativeSections_toQuotient hp f x)

/-- **A morphism of divided power thickenings from the global sections of an object with affine
thickened scheme to the relative sections of `T` comes from a morphism of `CRIS(X/S)`.**  This is
the universal property that `Crystalline.GlobalCrystallineSituation.homOfAffineSections` cannot
supply, because `T` need not have affine thickened scheme: the morphism of ambient divided power
schemes is realised by `Crystalline.DividedPowerScheme.homOfSectionsDPMorphism`, which only needs
the *target* to be affine, and the map on thickened schemes is forced through the closed fibre by
`Crystalline.SchemeThickening.sourceMapOfTargetMap`. -/
def homOfRelativeSections (f : T ⟶ A)
    (g : wholeThickeningToAffine hp B ⟶ relativeSections hp f) : T ⟶ B where
  sourceHom := SchemeThickening.sourceMapOfTargetMap
    (DividedPowerScheme.homOfSectionsDPMorphism g.hom)
  targetHom := DividedPowerScheme.homOfSectionsDPMorphism g.hom
  immersion_naturality := SchemeThickening.sourceMapOfTargetMap_immersion _
  base_naturality := homOfSectionsDPMorphism_base_naturality hp f g
  toX_naturality := homOfSectionsDPMorphism_toX_naturality hp f g

/-- The morphism of `CRIS(X/S)` produced by
`Crystalline.GlobalCrystallineSituation.homOfRelativeSections` induces the given morphism of
divided power thickenings. -/
theorem relativeSectionsMap_homOfRelativeSections (f : T ⟶ A)
    (g : wholeThickeningToAffine hp B ⟶ relativeSections hp f) :
    relativeSectionsMap hp f (homOfRelativeSections hp f g) = g :=
  DividedPowerThickening.Hom.ext
    (DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism g.hom)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **Passing to relative sections is functorial in the target**, contravariantly: postcomposing a
morphism `T ⟶ B` with a morphism `B ⟶ C` of objects with affine thickened scheme precomposes the
associated morphism of divided power thickenings with
`Crystalline.GlobalCrystallineSituation.wholeHomToAffine`. -/
theorem relativeSectionsMap_comp (f : T ⟶ A) (g : T ⟶ B) (h : B ⟶ C) :
    relativeSectionsMap hp f (g ≫ h) = wholeHomToAffine hp h ≫ relativeSectionsMap hp f g :=
  DividedPowerThickening.Hom.ext
    (globalSectionsDPMorphism_comp g.targetHom h.targetHom).symm

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **A morphism of `CRIS(X/S)` from an arbitrary object into one with affine thickened scheme is
determined by the morphism of divided power thickenings it induces.**  Together with
`Crystalline.GlobalCrystallineSituation.relativeSectionsMap_homOfRelativeSections` this makes the
relative sections construction a bijection on morphisms, which is the universal property the
binary product needs. -/
theorem relativeSectionsMap_injective (f : T ⟶ A) :
    Function.Injective (relativeSectionsMap hp f (B := B)) := fun _ _ e ↦
  hom_ext_of_appTop (CommRingCat.hom_ext (congrArg
    (fun k : wholeThickeningToAffine hp B ⟶ relativeSections hp f ↦ k.hom.toRingHom) e))

end Relative

section Limit

variable {A B P : Thickening S} [IsAffine A.thickening.source] [IsAffine B.thickening.source]
  [IsAffine P.thickening.source]
  {t : BinaryCofan (wholeThickeningToAffine hp A) (wholeThickeningToAffine hp B)}
  (ht : IsColimit t) (e : wholeThickeningToAffine hp P ≅ t.pt)

/-- **The morphism into the realisation of a coproduct induced by a cone with arbitrary vertex.**
A pair of morphisms `sf : T ⟶ A`, `sg : T ⟶ B` gives a pair of morphisms of divided power
thickenings into the relative sections of `T`; the coproduct property produces a single morphism
out of `t`, and `Crystalline.GlobalCrystallineSituation.homOfRelativeSections` turns it back into a
morphism `T ⟶ P` of `CRIS(X/S)`. -/
def liftOfIsColimit {T : Thickening S} (sf : T ⟶ A) (sg : T ⟶ B) : T ⟶ P :=
  homOfRelativeSections hp sf
    (e.hom ≫ (BinaryCofan.IsColimit.desc' ht
      (relativeSectionsMap hp sf sf) (relativeSectionsMap hp sf sg)).val)

/-- The morphism of divided power thickenings induced by
`Crystalline.GlobalCrystallineSituation.liftOfIsColimit` is the one the coproduct property
produces. -/
theorem relativeSectionsMap_liftOfIsColimit {T : Thickening S} (sf : T ⟶ A) (sg : T ⟶ B) :
    relativeSectionsMap hp sf (liftOfIsColimit hp ht e sf sg) =
      e.hom ≫ (BinaryCofan.IsColimit.desc' ht
        (relativeSectionsMap hp sf sf) (relativeSectionsMap hp sf sg)).val :=
  relativeSectionsMap_homOfRelativeSections hp sf _

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Precomposing with a morphism `f : P ⟶ A` inducing a coprojection `ι` turns the relative
sections map of `m ≫ f` into `ι` followed by `e.inv` and the relative sections map of `m`. -/
private theorem relativeSectionsMap_comp_eq_coprojection {C : Thickening S}
    [IsAffine C.thickening.source] {f : P ⟶ C} {ι : wholeThickeningToAffine hp C ⟶ t.pt}
    (hf : wholeHomToAffine hp f = ι ≫ e.inv) {T : Thickening S} (sf : T ⟶ A) (m : T ⟶ P) :
    relativeSectionsMap hp sf (m ≫ f) = ι ≫ e.inv ≫ relativeSectionsMap hp sf m := by
  rw [relativeSectionsMap_comp, hf, Category.assoc]

/-- The lift composed with the first projection is the first leg of the cone. -/
theorem liftOfIsColimit_comp_left {f : P ⟶ A} (hf : wholeHomToAffine hp f = t.inl ≫ e.inv)
    {T : Thickening S} (sf : T ⟶ A) (sg : T ⟶ B) :
    liftOfIsColimit hp ht e sf sg ≫ f = sf := by
  refine relativeSectionsMap_injective hp sf (B := A) ?_
  rw [relativeSectionsMap_comp_eq_coprojection hp e hf, relativeSectionsMap_liftOfIsColimit,
    Iso.inv_hom_id_assoc]
  exact (BinaryCofan.IsColimit.desc' ht
    (relativeSectionsMap hp sf sf) (relativeSectionsMap hp sf sg)).property.1

/-- The lift composed with the second projection is the second leg of the cone. -/
theorem liftOfIsColimit_comp_right {g : P ⟶ B} (hg : wholeHomToAffine hp g = t.inr ≫ e.inv)
    {T : Thickening S} (sf : T ⟶ A) (sg : T ⟶ B) :
    liftOfIsColimit hp ht e sf sg ≫ g = sg := by
  refine relativeSectionsMap_injective hp sf (B := B) ?_
  rw [relativeSectionsMap_comp_eq_coprojection hp e hg, relativeSectionsMap_liftOfIsColimit,
    Iso.inv_hom_id_assoc]
  exact (BinaryCofan.IsColimit.desc' ht
    (relativeSectionsMap hp sf sf) (relativeSectionsMap hp sf sg)).property.2

/-- **The lift is the only morphism compatible with both projections.**  A competitor induces, on
relative sections, a morphism out of the coproduct agreeing with the lift on both coprojections, so
the two agree; and a morphism of `CRIS(X/S)` into an object with affine thickened scheme is
determined by the morphism of divided power thickenings it induces. -/
theorem eq_liftOfIsColimit {f : P ⟶ A} {g : P ⟶ B}
    (hf : wholeHomToAffine hp f = t.inl ≫ e.inv) (hg : wholeHomToAffine hp g = t.inr ≫ e.inv)
    {T : Thickening S} (sf : T ⟶ A) (sg : T ⟶ B) (m : T ⟶ P) (hm₁ : m ≫ f = sf)
    (hm₂ : m ≫ g = sg) : m = liftOfIsColimit hp ht e sf sg := by
  refine relativeSectionsMap_injective hp sf (B := P) ?_
  rw [relativeSectionsMap_liftOfIsColimit]
  have key : e.inv ≫ relativeSectionsMap hp sf m =
      (BinaryCofan.IsColimit.desc' ht
        (relativeSectionsMap hp sf sf) (relativeSectionsMap hp sf sg)).val := by
    refine BinaryCofan.IsColimit.hom_ext ht ?_ ?_
    · rw [(BinaryCofan.IsColimit.desc' ht (relativeSectionsMap hp sf sf)
        (relativeSectionsMap hp sf sg)).property.1,
        ← relativeSectionsMap_comp_eq_coprojection hp e hf, hm₁]
    · rw [(BinaryCofan.IsColimit.desc' ht (relativeSectionsMap hp sf sf)
        (relativeSectionsMap hp sf sg)).property.2,
        ← relativeSectionsMap_comp_eq_coprojection hp e hg, hm₂]
  rw [← key, Iso.hom_inv_id_assoc]

/-- **A fan realising a coproduct of the rings of global sections is a product.**  Let `A`, `B` be
objects of `CRIS(X/S)` with affine thickened scheme, let `t` be a coproduct of their divided power
thickenings of global sections in `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`, and let `P` be an object with affine
thickened scheme whose divided power thickening of global sections is identified with `t` by `e`.
If `f : P ⟶ A` and `g : P ⟶ B` induce the two coprojections, then `P` with `f` and `g` is a product
of `A` and `B`.

The universal property is tested against an **arbitrary** object `T`, whose thickened scheme need
not be affine; the morphisms out of `T` are read off by
`Crystalline.GlobalCrystallineSituation.relativeSectionsMap`. -/
def isLimitBinaryFanOfIsColimit {f : P ⟶ A} {g : P ⟶ B}
    (hf : wholeHomToAffine hp f = t.inl ≫ e.inv)
    (hg : wholeHomToAffine hp g = t.inr ≫ e.inv) :
    IsLimit (BinaryFan.mk f g) :=
  BinaryFan.IsLimit.mk _ (liftOfIsColimit hp ht e) (liftOfIsColimit_comp_left hp ht e hf)
    (liftOfIsColimit_comp_right hp ht e hg) (eq_liftOfIsColimit hp ht e hf hg)

end Limit

end Constructions

/-- **Two objects of `CRIS(X/S)` with affine thickened schemes have a product**, for a global
crystalline situation with `X` and `S` affine and `p` nilpotent on `Γ(X, ⊤)`.  This is the affine
case of [Stacks, Tag 07I9].

The product is `Spec` of the coproduct of [Stacks, Tag 07HN]: the global sections of the two
objects are objects of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))`, their coproduct there is
`Crystalline.binaryCoproductWithTensorProductQuotient`, and
`Crystalline.GlobalCrystallineSituation.specThickeningOfAffine` realises it in `CRIS(X/S)`, with
`Crystalline.GlobalCrystallineSituation.specThickeningSectionsIso` identifying its global sections
with the coproduct.  The two projections come from the two coprojections through
`Crystalline.GlobalCrystallineSituation.homOfAffineSections`, and the universal property is
`Crystalline.GlobalCrystallineSituation.isLimitBinaryFanOfIsColimit`. -/
theorem hasBinaryProduct_of_isAffine {S : GlobalCrystallineSituation.{u}} [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (A B : Thickening S)
    [IsAffine A.thickening.source] [IsAffine B.thickening.source] :
    HasBinaryProduct A B := by
  obtain ⟨t, ht, -⟩ := binaryCoproductWithTensorProductQuotient
    (wholeThickeningToAffine hp A) (wholeThickeningToAffine hp B)
  exact HasLimit.mk ⟨_, isLimitBinaryFanOfIsColimit hp ht (specThickeningSectionsIso hp t.pt)
    (f := homOfAffineSections hp (t.inl ≫ (specThickeningSectionsIso hp t.pt).inv))
    (g := homOfAffineSections hp (t.inr ≫ (specThickeningSectionsIso hp t.pt).inv))
    (wholeHomToAffine_homOfAffineSections hp _) (wholeHomToAffine_homOfAffineSections hp _)⟩

end GlobalCrystallineSituation

end Crystalline

end
