module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionCrystallineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusBigGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEssSurj
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Cohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekExact

/-!
# `H⁰(Cris(X/S), 𝒪_{X/S})` in the example of [Stacks, Tag 07LJ]

Keep the situation of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionCrystallineSections`: `A = ℤ_p` with
the divided power ideal `(p)`, `C = 𝐅_p[x, y]/(x², xy, y²) = P/J` with `P = ℤ_p[x, y]`,
`X = Spec(C)`, `S = Spec(A)`, the divided power envelope `E = D_{P, γ}(J)` and the element
`τ = γ_p(x²) γ_p(y²) − γ_p(xy)²`.  This module draws the two conclusions of the example:

1. `H⁰(Cris(X/S), 𝒪_{X/S})` has `p`-torsion;
2. pulling back by Frobenius `F^* : H⁰(Cris(X/S), 𝒪_{X/S}) → H⁰(Cris(X/S), 𝒪_{X/S})` is not
   injective.

`H⁰(Cris(X/S), 𝒪_{X/S})` is the cohomology group
`(cohomologyFunctor (situation p) 0).obj (abelianSheaf (structureModule p))` of the abelian sheaf
underlying the structure sheaf, and it is identified with the ring `Γ(Cris(X/S), 𝒪_{X/S})` of
compatible families of sections (`Crystalline.TorsionExample.cohomologyZeroEquiv`).  The element
`τ` defines a class `Crystalline.TorsionExample.tauClass` there, through the global section
`Crystalline.TorsionExample.tauSection`, and:

* `p` kills it, because `p τ = 0` already in `E`;
* it is nonzero, because it is nonzero on the object of `CRIS(X/S)` attached to the example's
  witness thickening `(B, K, δ)`, where `τ` becomes `uv ≠ 0`;
* `F^*(τ) = σ(τ)` for every lift `σ` of Frobenius on `P`, and `F^*(τ) = 0` for the lift
  `x ↦ x^p`, `y ↦ y^p`.

The Frobenius pullback `F^*` is the action on global sections of the Frobenius morphism
`(F_X)_cris` of crystalline topoi, for the absolute Frobenius `F_X` of `X` over the identity of
`S` (the unique lift of the Frobenius of `𝐅_p` to `ℤ_p`): on the big crystalline site it is
`Crystalline.FCrystalSituation.frobeniusSectionRingHom`, reading a compatible family at the images
of the objects under the Frobenius endofunctor of `CRIS(X/S)`, and the global sections of
`Cris(X/S)` and of `CRIS(X/S)` agree by restriction
(`Crystalline.TorsionExample.bigSectionsRestrictEquiv`).

The source obtains the class of `τ` in `H⁰` from [Stacks, Proposition 60.21.3, Tag 07LG].  Here
it is constructed directly as a section over every object: in degree zero, what 07LG provides is
exactly that an element of `D` killed by `d` defines a global section, and for `τ` that is the
independence of the coordinates proved in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionTaylorInvariance` by Taylor's formula
from `dτ = 0`.

## Main definitions

* `Crystalline.TorsionExample.cohomologyZero` — `H⁰(Cris(X/S), 𝒪_{X/S})`, and
  `Crystalline.TorsionExample.cohomologyZeroEquiv` its identification with the ring of compatible
  families of sections of `𝒪_{X/S}` on `Cris(X/S)`.
* `Crystalline.TorsionExample.fSituation` — the Frobenius situation of the example, the lift of
  Frobenius on `ℤ_p` being the identity.
* `Crystalline.TorsionExample.frobeniusPullback` — `F^*` on `H⁰(Cris(X/S), 𝒪_{X/S})`.
* `Crystalline.TorsionExample.tauClass` — the class of `τ`.
* `Crystalline.TorsionExample.envelopeMapOfLift` — the map `σ` induced on the divided power
  envelope by a lift of Frobenius on `P`.

## Main results

* `Crystalline.TorsionExample.tauClass_ne_zero_and_prime_smul_eq_zero` — `τ` defines a nonzero
  element of `H⁰(Cris(X/S), 𝒪_{X/S})` killed by `p`.
* `Crystalline.TorsionExample.exists_ne_zero_prime_smul_eq_zero_cohomologyZero` — conclusion (1).
* `Crystalline.TorsionExample.frobeniusPullback_tauClass_eq_envelopeMapOfLift` — `F^*(τ) = σ(τ)`
  for the map `σ` induced by any lift of Frobenius on `P`.
* `Crystalline.TorsionExample.frobeniusPullback_tauClass` — `F^*(τ) = 0` for the lift
  `x ↦ x^p`, `y ↦ y^p`.
* `Crystalline.TorsionExample.not_injective_frobeniusPullback` — conclusion (2).

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DividedPowers Opposite
open Crystalline.DividedPowerScheme Crystalline.GlobalCrystallineSituation
open Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

/-! ### `H⁰(Cris(X/S), 𝒪_{X/S})` as the ring of compatible families -/

/-- **The crystalline structure sheaf `𝒪_{X/S}` as a module over itself.** -/
abbrev structureModule : SheafOfModules.{0} (structureSheaf (situation p)) :=
  SheafOfModules.unit _

/-- `H⁰(Cris(X/S), 𝒪_{X/S})`. -/
abbrev cohomologyZero : AddCommGrpCat.{1} :=
  (cohomologyFunctor (situation p) 0).obj (abelianSheaf (structureModule p))

/-- The cone over the abelian sheaf `𝒪_{X/S}` whose point is the ring of compatible families. -/
def sectionsCone : Cone (abelianSheaf (structureModule p)).obj where
  pt := AddCommGrpCat.of (crystallineSectionRing (situation p))
  π :=
    { app := fun A => AddCommGrpCat.ofHom
        { toFun := fun s => ULift.up (s.val A)
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality := fun A B f => by
        ext s
        exact congrArg ULift.up (s.property f).symm }

variable {p}

/-- The compatible family of a global section of `𝒪_{X/S}`. -/
def familyOfGlobalSection
    (x : (globalSections (situation p)).obj (abelianSheaf (structureModule p))) :
    crystallineSectionRing (situation p) :=
  ⟨fun A => (Sheaf.ΓRes (abelianSheaf (structureModule p)) A x).down, fun {A B} f => by
    have h := ConcreteCategory.congr_hom (Sheaf.ΓRes_map (abelianSheaf (structureModule p)) f) x
    exact congrArg ULift.down h⟩

variable (p)

/-- **`Γ(Cris(X/S), 𝒪_{X/S})` is the ring of compatible families of sections**, as abelian
groups: global sections are the limit of the presheaf, with the restriction maps as legs. -/
def globalSectionsEquiv :
    (globalSections (situation p)).obj (abelianSheaf (structureModule p)) ≃+
      crystallineSectionRing (situation p) where
  toFun := familyOfGlobalSection
  invFun s := ((Sheaf.isLimitConeΓ (abelianSheaf (structureModule p))).lift (sectionsCone p)) s
  left_inv x := by
    refine Concrete.isLimit_ext _ (Sheaf.isLimitConeΓ (abelianSheaf (structureModule p))) _ _
      fun A => ?_
    have h := ConcreteCategory.congr_hom
      ((Sheaf.isLimitConeΓ (abelianSheaf (structureModule p))).fac (sectionsCone p) A)
      (familyOfGlobalSection x)
    exact h.trans rfl
  right_inv s := by
    refine Subtype.ext (funext fun A => ?_)
    have h := ConcreteCategory.congr_hom
      ((Sheaf.isLimitConeΓ (abelianSheaf (structureModule p))).fac (sectionsCone p) A) s
    exact congrArg ULift.down h
  map_add' x y := by
    refine Subtype.ext (funext fun A => ?_)
    change (Sheaf.ΓRes (abelianSheaf (structureModule p)) A (x + y)).down =
      (Sheaf.ΓRes (abelianSheaf (structureModule p)) A x).down +
        (Sheaf.ΓRes (abelianSheaf (structureModule p)) A y).down
    rw [map_add]
    rfl

/-- **`H⁰(Cris(X/S), 𝒪_{X/S}) = Γ(Cris(X/S), 𝒪_{X/S})`**, read as the ring of compatible families
of sections `(a_{(U,T,δ)} ∈ Γ(T, 𝒪_T))`. -/
def cohomologyZeroEquiv : cohomologyZero p ≃+ crystallineSectionRing (situation p) :=
  ((cohomologyFunctorZeroIso (situation p)).app
    (abelianSheaf (structureModule p))).addCommGroupIsoToAddEquiv.trans (globalSectionsEquiv p)

/-! ### The global sections of `Cris(X/S)` and of `CRIS(X/S)` -/

/-- The structure sheaf of `CRIS(X/S)` as a sheaf of sets. -/
theorem isSheaf_crystallineStructureSheaf_forget :
    Presheaf.IsSheaf (topology (situation p))
      ((crystallineStructureSheaf (situation p)).val ⋙ CategoryTheory.forget RingCat.{0}) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (crystallineStructureSheaf (situation p)).property

/-- Restriction of a compatible family on `CRIS(X/S)` to `Cris(X/S)`. -/
def bigSectionsRestrict :
    bigCrystallineSectionRing (situation p) →+* crystallineSectionRing (situation p) where
  toFun a := ⟨fun A => a.val (op ((CrystallineThickening.ι (situation p)).obj A.unop)),
    fun f => a.property ((CrystallineThickening.ι (situation p)).map f.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction to `Cris(X/S)` is injective, the objects of `Cris(X/S)` covering the final
object of the topos of `CRIS(X/S)`. -/
theorem bigSectionsRestrict_injective : Function.Injective (bigSectionsRestrict p) := by
  intro x y hxy
  have h := (CrystallineThickening.coversTop_ι (situation p)).sections_ext
    ⟨_, isSheaf_crystallineStructureSheaf_forget p⟩ (x := ⟨x.1, x.2⟩) (y := ⟨y.1, y.2⟩)
    fun A => congrArg (fun t : crystallineSectionRing (situation p) => t.val (op A)) hxy
  exact Subtype.ext (congrArg Subtype.val h)

/-- Restriction to `Cris(X/S)` is surjective: a compatible family over `Cris(X/S)` glues, the
objects of `Cris(X/S)` under an object of `CRIS(X/S)` being cofiltered. -/
theorem bigSectionsRestrict_surjective : Function.Surjective (bigSectionsRestrict p) := by
  intro t
  set F := (crystallineStructureSheaf (situation p)).obj ⋙ CategoryTheory.forget RingCat.{0}
  have hcomp : (show Presheaf.FamilyOfElementsOnObjects F
      (CrystallineThickening.ι (situation p)).obj from fun A => t.val (op A)).IsCompatible := by
    intro Z i j f g
    obtain ⟨W, a, b, -⟩ := (isCofilteredOrEmpty_structuredArrow_ι (situation p) Z).cone_objs
      (StructuredArrow.mk f) (StructuredArrow.mk g)
    have hf' : W.hom ≫ (CrystallineThickening.ι (situation p)).map a.right = f :=
      StructuredArrow.w a
    have hg' : W.hom ≫ (CrystallineThickening.ι (situation p)).map b.right = g :=
      StructuredArrow.w b
    have ha : F.map ((CrystallineThickening.ι (situation p)).map a.right).op (t.val (op i)) =
        t.val (op W.right) := t.property a.right.op
    have hb : F.map ((CrystallineThickening.ι (situation p)).map b.right).op (t.val (op j)) =
        t.val (op W.right) := t.property b.right.op
    rw [← hf', ← hg', op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply, ha, hb]
  refine ⟨⟨(hcomp.section_ (CrystallineThickening.coversTop_ι (situation p))
    (isSheaf_crystallineStructureSheaf_forget p)).1,
    (hcomp.section_ (CrystallineThickening.coversTop_ι (situation p))
    (isSheaf_crystallineStructureSheaf_forget p)).2⟩, Subtype.ext (funext fun A => ?_)⟩
  exact (hcomp.section_apply (CrystallineThickening.coversTop_ι (situation p))
    (isSheaf_crystallineStructureSheaf_forget p) A.unop).trans rfl

/-- **`Γ(CRIS(X/S), 𝒪_{X/S}) = Γ(Cris(X/S), 𝒪_{X/S})`**: restricting to the small crystalline site
loses no global section of the structure sheaf. -/
def bigSectionsRestrictEquiv :
    bigCrystallineSectionRing (situation p) ≃+* crystallineSectionRing (situation p) :=
  RingEquiv.ofBijective (bigSectionsRestrict p)
    ⟨bigSectionsRestrict_injective p, bigSectionsRestrict_surjective p⟩

/-! ### Ring maps out of `ℤ_p` into a ring in which `p` vanishes -/

/-- **Two ring maps `ℤ_p → R` agree as soon as `p = 0` in `R`**: `a − r ∈ (p)` for the integer
representative `r` of `a` modulo `p`. -/
theorem padicInt_ringHom_ext {R : Type*} [CommRing R] (hR : (p : R) = 0) (f g : ℤ_[p] →+* R) :
    f = g := by
  ext a
  have key : ∀ h : ℤ_[p] →+* R, h a = (PadicInt.zmodRepr a : R) := by
    intro h
    have hmem := PadicInt.sub_zmodRepr_mem a
    rw [PadicInt.maximalIdeal_eq_span_p] at hmem
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
    have h0 : h (a - PadicInt.zmodRepr a) = 0 := by rw [hb, map_mul, map_natCast, hR, zero_mul]
    rwa [map_sub, map_natCast, sub_eq_zero] at h0
  rw [key f, key g]

/-- `ℤ_p → Γ(S, 𝒪_S)` is a retraction of the inverse of `Γ(S, 𝒪_S) ≅ ℤ_p`. -/
private theorem baseUnit_ΓSpecIso_hom_apply (x : (situation p).S.scheme.sheaf.obj.obj (op ⊤)) :
    (baseUnit (p := p)) ((Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom x) = x :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom_inv_id x

/-- Two ring maps `Γ(S, 𝒪_S) = ℤ_p → R` agree as soon as `p = 0` in `R`. -/
theorem baseSections_ringHom_ext {R : Type*} [CommRing R] (hR : (p : R) = 0)
    (f g : Γ((situation p).S.scheme, ⊤) →+* R) : f = g := by
  have h := padicInt_ringHom_ext p hR (f.comp ((baseUnit (p := p)))) (g.comp ((baseUnit (p := p))))
  ext x
  rw [← baseUnit_ΓSpecIso_hom_apply p x]
  exact congrArg (fun φ : ℤ_[p] →+* R => φ ((Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom x)) h

/-! ### The Frobenius situation -/

/-- `p` lies in the divided power ideal of `ℤ_p`. -/
private theorem prime_mem_base_ideal : (p : base p) ∈ (base p).ideal :=
  Ideal.subset_span (by simp)

/-- `p` lies in the divided power ideal of `Γ(S, 𝒪_S)`. -/
theorem prime_mem_baseSectionsIdeal :
    ((situation p).p : (situation p).S.scheme.sheaf.obj.obj (op ⊤)) ∈
      (situation p).S.ideal.obj (op ⊤) := by
  have h := (specDividedPowerSchemeUnit (base p)).ideal_comp
    (Ideal.mem_map_of_mem _ (prime_mem_base_ideal p))
  rw [map_natCast] at h
  exact h

/-- **Every element of `Γ(S, 𝒪_S) = ℤ_p` is congruent to its `p`-th power modulo `p`**, so that
the identity of `ℤ_p` lifts the Frobenius of `𝐅_p`. -/
theorem sub_pow_mem_base (x : (situation p).S.scheme.sheaf.obj.obj (op ⊤)) :
    ∃ y : (situation p).S.scheme.sheaf.obj.obj (op ⊤), x - x ^ (situation p).p =
      ((situation p).p : (situation p).S.scheme.sheaf.obj.obj (op ⊤)) * y := by
  set a := (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).hom.hom x
  have ha : a - a ^ p ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub,
      map_pow, ZMod.pow_card, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hx : (baseUnit (p := p)) a = x := baseUnit_ΓSpecIso_hom_apply p x
  refine ⟨(baseUnit (p := p)) b, ?_⟩
  have key := congrArg (baseUnit (p := p)) hb
  rw [map_sub, map_pow, map_mul, map_natCast, hx] at key
  exact key

/-- **The Frobenius situation of the example**: the identity of `ℤ_p`, the unique ring
endomorphism of `ℤ_p` and a lift of the Frobenius of `𝐅_p`, so that `F^*` is pullback along the
absolute Frobenius `F_X` of `X` over `S`. -/
def fSituation : FCrystalSituation.{0} where
  global := situation p
  prime_mem := prime_mem_baseSectionsIdeal p
  sigma := DPMorphism.id _
  sigma_mod_prime := sub_pow_mem_base p

/-- **Pulling back by Frobenius `F^* : H⁰(Cris(X/S), 𝒪_{X/S}) → H⁰(Cris(X/S), 𝒪_{X/S})`**: the
action of the Frobenius morphism `(F_X)_cris` of crystalline topoi on global sections of the
structure sheaf, `Crystalline.FCrystalSituation.frobeniusSectionRingHom` on `Γ(CRIS(X/S), 𝒪)`,
read on `H⁰(Cris(X/S), 𝒪_{X/S}) = Γ(Cris(X/S), 𝒪_{X/S}) = Γ(CRIS(X/S), 𝒪_{X/S})`. -/
def frobeniusPullback : cohomologyZero p →+ cohomologyZero p :=
  (cohomologyZeroEquiv p).symm.toAddMonoidHom.comp
    ((bigSectionsRestrictEquiv p).toRingHom.toAddMonoidHom.comp
      ((FCrystalSituation.frobeniusSectionRingHom (fSituation p)).toAddMonoidHom.comp
        ((bigSectionsRestrictEquiv p).symm.toRingHom.toAddMonoidHom.comp
          (cohomologyZeroEquiv p).toAddMonoidHom)))

/-! ### The class of `τ` -/

/-- **The class of `τ` in `H⁰(Cris(X/S), 𝒪_{X/S})`**, the global section
`Crystalline.TorsionExample.tauSection`. -/
def tauClass : cohomologyZero p := (cohomologyZeroEquiv p).symm tauSection

/-- The global section of `CRIS(X/S)` restricting to `tauSection`. -/
abbrev bigTauSection : bigCrystallineSectionRing (situation p) :=
  (bigSectionsRestrictEquiv p).symm tauSection

/-- The thickened scheme `Spec(B/J)` of the object of `CRIS(X/S)` attached to an object
`(B, J, δ)` of `CRIS(C/A)` is affine. -/
instance isAffine_specThickeningOfAffine
    (T : DividedPowerThickening.{0, 0, 0} (affineSituation (situation p)
      (prime_isNilpotent_sections p))) :
    IsAffine (specThickeningOfAffine (prime_isNilpotent_sections p) T).thickening.source :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (↥T.ring ⧸ T.ring.ideal))))

/-- **The value of the global section defined by `τ` on an object of `CRIS(X/S)` with affine
thickened scheme is `tauAt`.**  The object maps to a thickening of the whole of `X`
(`Crystalline.GlobalCrystallineSituation.exists_hom_to_specWholeSpaceThickening`), an object of
`Cris(X/S)`, where the value is `tauAt` by definition, and `tauAt` is compatible with
restriction. -/
theorem bigTauSection_val (B : Thickening (situation p)) [IsAffine B.thickening.source] :
    (bigTauSection p).val (op B) = tauAt B := by
  obtain ⟨T, hT, ⟨m⟩⟩ := exists_hom_to_specWholeSpaceThickening (prime_isNilpotent_sections p) B
  have h1 : (bigTauSection p).val (op (specThickeningOfAffine (prime_isNilpotent_sections p) T)) =
      tauAt (specThickeningOfAffine (prime_isNilpotent_sections p) T) :=
    congrArg (fun t : crystallineSectionRing (situation p) =>
      t.val (op (specWholeSpaceThickening (prime_isNilpotent_sections p) T hT).obj))
      ((bigSectionsRestrictEquiv p).apply_symm_apply tauSection)
  have h2 : (crystallineStructureSheaf (situation p)).obj.map m.op
      ((bigTauSection p).val (op (specThickeningOfAffine (prime_isNilpotent_sections p) T))) =
      (bigTauSection p).val (op B) := (bigTauSection p).property m.op
  rw [← h2, h1]
  exact tauAt_map m

/-- `p = 0` in the witness ring `B`, an `𝐅_p`-algebra. -/
theorem witnessRing_prime_eq_zero : ((p : ℕ) : DividedPowers.TorsionWitness.Witness p) = 0 :=
  DividedPowers.TorsionWitness.natCast_eq_zero p

/-- `J` maps into `K` under the presentation `P → B` of the witness ring. -/
theorem relations_map_le_K :
    (relations p).map (DividedPowers.TorsionWitness.mvPolynomialHom p) ≤
      DividedPowers.TorsionWitness.K p := by
  have hrel : relations p = Ideal.span ({(p : polynomial p), polynomialX p ^ 2,
      polynomialX p * polynomialY p, polynomialY p ^ 2} : Set (polynomial p)) := rfl
  rw [hrel, Ideal.map_span, Ideal.span_le]
  rintro z ⟨w, hw, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  obtain rfl | rfl | rfl | rfl := hw
  · rw [SetLike.mem_coe, map_natCast, DividedPowers.TorsionWitness.natCast_eq_zero]
    exact (DividedPowers.TorsionWitness.K p).zero_mem
  · rw [SetLike.mem_coe, map_pow, DividedPowers.TorsionWitness.mvPolynomialHom_X_zero]
    exact DividedPowers.TorsionWitness.x_sq_mem p
  · rw [SetLike.mem_coe, map_mul, DividedPowers.TorsionWitness.mvPolynomialHom_X_zero,
      DividedPowers.TorsionWitness.mvPolynomialHom_X_one,
      DividedPowers.TorsionWitness.x_mul_y_eq_zero]
    exact (DividedPowers.TorsionWitness.K p).zero_mem
  · rw [SetLike.mem_coe, map_pow, DividedPowers.TorsionWitness.mvPolynomialHom_X_one]
    exact DividedPowers.TorsionWitness.y_sq_mem p

/-- The map `C → B/K` of the witness thickening. -/
def witnessQuotient :
    quotientRing p →+* DividedPowers.TorsionWitness.Witness p ⧸ DividedPowers.TorsionWitness.K p :=
  Ideal.Quotient.lift (relations p)
    ((Ideal.Quotient.mk (DividedPowers.TorsionWitness.K p)).comp
      (DividedPowers.TorsionWitness.mvPolynomialHom p))
    fun _ hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      (relations_map_le_K p (Ideal.mem_map_of_mem _ hf))

/-- **The witness thickening `(B, K, δ)` of [Stacks, Tag 07LJ] as an object of `CRIS(C/A)`**, over
`A = Γ(S, 𝒪_S)` and `C = Γ(X, 𝒪_X)`. -/
def witnessThickening :
    DividedPowerThickening.{0, 0, 0}
      (affineSituation (situation p) (prime_isNilpotent_sections p)) where
  ring := witnessRing p
  fromBase := (specSectionsRingIso (base p)).inv ≫ witnessStructureMap p
  prime_nilpotent := ⟨1, by rw [pow_one]; exact witnessRing_prime_eq_zero p⟩
  toQuotient := (witnessQuotient p).comp (Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).hom.hom
  commutes := baseSections_ringHom_ext p (by
      rw [← map_natCast (Ideal.Quotient.mk (DividedPowers.TorsionWitness.K p)),
        witnessRing_prime_eq_zero, map_zero]) _ _

/-- **The object of `CRIS(X/S)` attached to the witness thickening**:
`Spec(B/K) ↪ Spec(B, K, δ)` over `X`. -/
abbrev witnessObject : Thickening (situation p) :=
  specThickeningOfAffine (prime_isNilpotent_sections p) (witnessThickening p)

/-- **`τ` becomes `uv` on the witness object.** -/
theorem tauAt_witnessObject :
    tauAt (witnessObject p) = toSections (B := witnessObject p)
      (specSectionsRingIso (witnessRing p)).hom
        (DividedPowers.TorsionWitness.u p * DividedPowers.TorsionWitness.v p) := by
  rw [← toWitnessRing_envelopeTau]
  refine (tauAt_eq (witnessObject p)
    (toWitnessRing p ≫ (specSectionsRingIso (witnessRing p)).hom) ?_ ?_).symm
  · refine DFunLike.ext _ _ fun r => ?_
    have hR : ((p : ℕ) : Γ((witnessObject p).thickening.target.scheme, ⊤)) = 0 := by
      show ((p : ℕ) : Γ(Spec (CommRingCat.of (DividedPowers.TorsionWitness.Witness p)), ⊤)) = 0
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of
        (DividedPowers.TorsionWitness.Witness p))).inv.hom, witnessRing_prime_eq_zero, map_zero]
    exact congrArg (fun φ : ℤ_[p] →+* Γ((witnessObject p).thickening.target.scheme, ⊤) => φ r)
      (padicInt_ringHom_ext p hR _ _)
  · intro i
    refine appTop_specQuotientImmersion_eq (prime_isNilpotent_sections p) (witnessThickening p) ?_
    show Ideal.Quotient.mk _ (toWitnessRing p ((envelope p).algebraMap.toRingHom
      (MvPolynomial.X i))) = witnessQuotient p
        ((Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).hom.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).inv.hom
            (Ideal.Quotient.mk (relations p) (MvPolynomial.X i))))
    have hii : (Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).inv.hom
          (Ideal.Quotient.mk (relations p) (MvPolynomial.X i))) =
        Ideal.Quotient.mk (relations p) (MvPolynomial.X i) :=
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (quotientRing p))).inv_hom_id _
    rw [toWitnessRing_algebraMap, hii]
    rfl

/-- `τ` does not vanish on the witness object, `uv` being nonzero in `B`. -/
theorem tauAt_witnessObject_ne_zero : tauAt (witnessObject p) ≠ 0 := by
  rw [tauAt_witnessObject]
  intro h
  refine DividedPowers.TorsionWitness.u_mul_v_ne_zero p ?_
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of
      (DividedPowers.TorsionWitness.Witness p))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso _).injective
  exact hinj (h.trans (map_zero (Scheme.ΓSpecIso (CommRingCat.of
      (DividedPowers.TorsionWitness.Witness p))).inv.hom).symm)

/-- **The global section defined by `τ` is nonzero.** -/
theorem tauSection_ne_zero : tauSection (p := p) ≠ 0 := by
  intro h
  have h1 := bigTauSection_val p (witnessObject p)
  have h0 : bigTauSection p = 0 := by rw [bigTauSection, h, map_zero]
  rw [h0] at h1
  exact tauAt_witnessObject_ne_zero p h1.symm

/-! ### The Frobenius pullback of `τ` -/

/-- The image of an object of `CRIS(X/S)` under the Frobenius endofunctor has the same thickened
scheme. -/
instance isAffine_frobeniusChangeBase (B : Thickening (situation p))
    [IsAffine B.thickening.source] :
    IsAffine (((fSituation p).frobeniusChangeBase).obj B).thickening.source :=
  inferInstanceAs (IsAffine B.thickening.source)

/-- **`F^*(τ) = σ(τ)` on every object**: for a divided power endomorphism `σ` of `E` over `A`
lifting the Frobenius (`σ(y_i) − y_i^p` in the divided power ideal), the image of `τ` on the
Frobenius pullback of an object `(U, T, δ)` is the image of `σ(τ)` under the lift
`E → Γ(T, 𝒪_T)`. -/
theorem tauAt_frobeniusChangeBase (B : Thickening (situation p)) [IsAffine B.thickening.source]
    (σ : DPMorphism (envelope p).object.dividedPowers (envelope p).object.dividedPowers)
    (hσ : σ.comp (envelope p).structureMap = (envelope p).structureMap)
    (hσi : ∀ i, σ (envelopeCoord (envelope p) i) - envelopeCoord (envelope p) i ^ p ∈
      (envelope p).object.ideal) :
    tauAt (((fSituation p).frobeniusChangeBase).obj B) =
      toSections (envelopeLift B) (σ (envelopeTau p)) := by
  refine (tauAt_eq (((fSituation p).frobeniusChangeBase).obj B) ((envelopeLift B).comp σ) ?_
    ?_).symm
  · refine DFunLike.ext _ _ fun r => ?_
    have h1 := DFunLike.congr_fun hσ r
    have h2 := DFunLike.congr_fun (envelopeLift_comp_structureMap B) r
    show toSections (envelopeLift B) (σ ((envelope p).structureMap r)) =
      ((B.toBase ≫ (fSituation p).specSigma).hom).appTop.hom ((baseUnit (p := p)) r)
    change σ ((envelope p).structureMap r) = (envelope p).structureMap r at h1
    change toSections (envelopeLift B) ((envelope p).structureMap r) =
      B.toBase.hom.appTop.hom ((baseUnit (p := p)) r) at h2
    have hσS : (fSituation p).specSigma.hom.appTop.hom ((baseUnit (p := p)) r) =
        (baseUnit (p := p)) r :=
      (ConcreteCategory.congr_hom (fSituation p).specSigma_appTop ((baseUnit (p := p)) r)).trans
        rfl
    rw [h1, h2]
    exact (congrArg B.toBase.hom.appTop.hom hσS).symm.trans
      (Stacks.Thickenings.appTop_comp_apply _ _ _)
  · intro i
    obtain hmem := hσi i
    have hker : B.thickening.immersion.appTop.hom (toSections (envelopeLift B)
        (σ (envelopeCoord (envelope p) i) - envelopeCoord (envelope p) i ^ p)) = 0 := by
      have := (envelopeLift B).ideal_comp (Ideal.mem_map_of_mem _ hmem)
      exact (SchemeThickening.mem_sectionsIdeal_iff B.thickening _).mp this
    rw [map_sub, map_sub, map_pow, map_pow, envelopeLift_coord, immersion_liftValues,
      sub_eq_zero] at hker
    show B.thickening.immersion.appTop.hom (toSections (envelopeLift B)
      (σ (envelopeCoord (envelope p) i))) =
        ((B.toX ≫ (fSituation p).frobenius)).appTop.hom (coordinate p i)
    rw [hker]
    refine Eq.trans ?_ (Stacks.Thickenings.appTop_comp_apply B.toX (fSituation p).frobenius
      (coordinate p i))
    have hF : (fSituation p).frobenius.appTop.hom (coordinate p i) = coordinate p i ^ p :=
      Stacks.Frobenius.absoluteFrobenius_app_apply _ _ _ ⊤ _
    exact (map_pow B.toX.appTop.hom _ _).symm.trans (congrArg B.toX.appTop.hom hF.symm)

/-- The value of `F^*(τ)` on an object of `Cris(X/S)`. -/
theorem cohomologyZeroEquiv_frobeniusPullback_tauClass
    (A : (GlobalCrystallineSituation.CrystallineThickening (situation p))ᵒᵖ) :
    (cohomologyZeroEquiv p (frobeniusPullback p (tauClass p))).val A =
      tauAt (((fSituation p).frobeniusChangeBase).obj A.unop.obj) := by
  have h : cohomologyZeroEquiv p (frobeniusPullback p (tauClass p)) =
      bigSectionsRestrict p (FCrystalSituation.frobeniusSectionRingHom (fSituation p)
        (bigTauSection p)) := by
    simp only [frobeniusPullback, tauClass, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    show bigSectionsRestrictEquiv p (FCrystalSituation.frobeniusSectionRingHom (fSituation p)
      ((bigSectionsRestrictEquiv p).symm (cohomologyZeroEquiv p
        ((cohomologyZeroEquiv p).symm tauSection)))) = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact bigTauSection_val p (((fSituation p).frobeniusChangeBase).obj A.unop.obj)

/-- **`F^*(τ) = σ(τ)`**, [Stacks, Tag 07LJ]: for every lift `σ` of Frobenius to the divided power
envelope over `A`, the class `F^*(τ)` has, on every object `(U, T, δ)` of `Cris(X/S)`, the value
of `σ(τ)` under the lift `E → Γ(T, 𝒪_T)` of the coordinates — that is, `F^*(τ)` is the class
defined by `σ(τ)`. -/
theorem frobeniusPullback_tauClass_eq
    (σ : DPMorphism (envelope p).object.dividedPowers (envelope p).object.dividedPowers)
    (hσ : σ.comp (envelope p).structureMap = (envelope p).structureMap)
    (hσi : ∀ i, σ (envelopeCoord (envelope p) i) - envelopeCoord (envelope p) i ^ p ∈
      (envelope p).object.ideal)
    (A : GlobalCrystallineSituation.CrystallineThickening (situation p)) :
    (cohomologyZeroEquiv p (frobeniusPullback p (tauClass p))).val (op A) =
      toSections (envelopeLift A.obj) (σ (envelopeTau p)) :=
  (cohomologyZeroEquiv_frobeniusPullback_tauClass p (op A)).trans
    (tauAt_frobeniusChangeBase p A.obj σ hσ hσi)

/-! ### Lifts of Frobenius on `P` -/

/-- A lift `φ` of Frobenius on `P` (an endomorphism of `ℤ_p`-algebras with `φ(f) ≡ f^p` modulo
`p`) carries `J` into `J`, `J` containing `p` and the `p`-th powers of its elements. -/
theorem relations_map_le_of_lift (φ : polynomial p →ₐ[ℤ_[p]] polynomial p)
    (hφ : ∀ f, φ f - f ^ p ∈ Ideal.span {(p : polynomial p)}) :
    (relations p).map φ ≤ relations p := by
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  have hpJ : Ideal.span {(p : polynomial p)} ≤ relations p :=
    Ideal.span_le.mpr (by
      rw [Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp))
  have h1 : g ^ p ∈ relations p := Ideal.pow_mem_of_mem _ hg p (Fact.out : p.Prime).pos
  have h2 := hpJ (hφ g)
  rw [Ideal.mem_comap]
  simpa using (relations p).add_mem h1 h2

/-- The divided power endomorphism of `E` over `A` induced by a lift `φ` of Frobenius on `P`
exists. -/
theorem exists_envelopeMapOfLift (φ : polynomial p →ₐ[ℤ_[p]] polynomial p)
    (hφ : ∀ f, φ f - f ^ p ∈ Ideal.span {(p : polynomial p)}) :
    ∃ q : DPMorphism (envelope p).object.dividedPowers (envelope p).object.dividedPowers,
      q.comp (envelope p).structureMap = (envelope p).structureMap ∧
        ∀ i, q (envelopeCoord (envelope p) i) =
          (envelope p).algebraMap.toRingHom (φ (MvPolynomial.X i)) := by
  refine exists_envelope_dpMorphism (envelope p) (envelope p).object (envelope p).structureMap _ ?_
  have heq : MvPolynomial.eval₂Hom (envelope p).structureMap.toRingHom
      (fun i => (envelope p).algebraMap.toRingHom (φ (MvPolynomial.X i))) =
      (envelope p).algebraMap.toRingHom.comp φ.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (congrArg (fun g : ↥(base p) →+* (envelope p).object => g r)
        (envelope p).algebraMap_comp).symm
    · rw [MvPolynomial.eval₂Hom_X']
      rfl
  rw [heq, ← Ideal.map_map]
  exact (Ideal.map_mono (relations_map_le_of_lift p φ hφ)).trans (envelope p).algebraMap.ideal_comp

/-- **The map `σ` induced on the divided power envelope by a lift `φ` of Frobenius on `P`**: the
divided power endomorphism of `E = D_{P, γ}(J)` over `A` extending `φ`. -/
def envelopeMapOfLift (φ : polynomial p →ₐ[ℤ_[p]] polynomial p)
    (hφ : ∀ f, φ f - f ^ p ∈ Ideal.span {(p : polynomial p)}) :
    DPMorphism (envelope p).object.dividedPowers (envelope p).object.dividedPowers :=
  (exists_envelopeMapOfLift p φ hφ).choose

/-- **`F^*(τ) = σ(τ)`**: for every lift `φ` of Frobenius on `P` and the map `σ` it induces on the
divided power envelope, the class `F^*(τ) ∈ H⁰(Cris(X/S), 𝒪_{X/S})` is the class defined by
`σ(τ)`: on every object `(U, T, δ)` of `Cris(X/S)` its value is the image of `σ(τ)` under a lift
`E → Γ(T, 𝒪_T)` of the coordinates. -/
@[stacks 07LJ "F^*(τ) = σ(τ): for every lift φ of Frobenius on P = ZZ_p[x, y] over ZZ_p, with σ \
the map it induces on the divided power envelope, the Frobenius pullback of the class of τ in \
H^0(Cris(X/S), O_{X/S}) is the class defined by σ(τ)"]
theorem frobeniusPullback_tauClass_eq_envelopeMapOfLift
    (φ : polynomial p →ₐ[ℤ_[p]] polynomial p)
    (hφ : ∀ f, φ f - f ^ p ∈ Ideal.span {(p : polynomial p)})
    (A : GlobalCrystallineSituation.CrystallineThickening (situation p)) :
    (cohomologyZeroEquiv p (frobeniusPullback p (tauClass p))).val (op A) =
      toSections (envelopeLift A.obj) (envelopeMapOfLift p φ hφ (envelopeTau p)) := by
  obtain ⟨hcomp, hcoord⟩ := (exists_envelopeMapOfLift p φ hφ).choose_spec
  refine frobeniusPullback_tauClass_eq p _ hcomp (fun i => ?_) A
  have hpE : (p : (envelope p).object) ∈ (envelope p).object.ideal := by
    simpa using (envelope p).structureMap.ideal_comp
      (Ideal.mem_map_of_mem (envelope p).structureMap.toRingHom (prime_mem_base_ideal p))
  show envelopeMapOfLift p φ hφ (envelopeCoord (envelope p) i) - _ ∈ _
  rw [envelopeMapOfLift, hcoord, envelopeCoord, ← map_pow, ← map_sub]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hφ (MvPolynomial.X i))
  rw [hc, map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ hpE

/-- **`F^*(τ) = 0`** for the lift of Frobenius `x ↦ x^p`, `y ↦ y^p`: the class `F^*(τ) = σ(τ)`
vanishes, as `σ(τ) = γ_p(x^{2p}) γ_p(y^{2p}) − γ_p(x^p y^p)² = 0`. -/
@[stacks 07LJ "for the lift of Frobenius x ↦ x^p, y ↦ y^p one has F^*(τ) = 0 in \
H^0(Cris(X/S), O_{X/S})"]
theorem frobeniusPullback_tauClass : frobeniusPullback p (tauClass p) = 0 := by
  refine (cohomologyZeroEquiv p).injective (Subtype.ext (funext fun A => ?_))
  rw [frobeniusPullback_tauClass_eq p (envelopeFrobenius p)
    (envelopeFrobenius_comp_structureMap p) (fun i => by
      rw [envelopeFrobenius_coord, sub_self]; exact Ideal.zero_mem _) A.unop,
    envelopeFrobenius_envelopeTau, map_zero, map_zero]
  rfl

/-- **`τ` defines a nonzero class in `H⁰(Cris(X/S), 𝒪_{X/S})`.** -/
theorem tauClass_ne_zero : tauClass p ≠ 0 := by
  intro h
  apply tauSection_ne_zero p
  rw [← (cohomologyZeroEquiv p).apply_symm_apply tauSection]
  show cohomologyZeroEquiv p (tauClass p) = 0
  rw [h, map_zero]

/-- **The class of `τ` is killed by `p`.** -/
theorem prime_smul_tauClass : p • tauClass p = 0 := by
  rw [tauClass, ← map_nsmul, nsmul_eq_mul, prime_mul_tauSection, map_zero]

/-- **`τ` defines a nonzero `p`-torsion element of `H⁰(Cris(X/S), 𝒪_{X/S})`.** -/
@[stacks 07LJ "τ defines a nonzero element of H^0(Cris(X/S), O_{X/S}) killed by p, for \
X = Spec(F_p[x, y]/(x^2, xy, y^2)) and S = Spec(ZZ_p) with the divided power ideal (p)"]
theorem tauClass_ne_zero_and_prime_smul_eq_zero : tauClass p ≠ 0 ∧ p • tauClass p = 0 :=
  ⟨tauClass_ne_zero p, prime_smul_tauClass p⟩

/-- **`H⁰(Cris(X/S), 𝒪_{X/S})` has `p`-torsion**, for `X = Spec(𝐅_p[x, y]/(x², xy, y²))` and
`S = Spec(ℤ_p)` with the divided power ideal `(p)` and its divided powers. -/
@[stacks 07LJ "conclusion (1): H^0(Cris(X/S), O_{X/S}) has p-torsion, for \
X = Spec(F_p[x, y]/(x^2, xy, y^2)) and S = Spec(ZZ_p) with the divided power ideal (p)"]
theorem exists_ne_zero_prime_smul_eq_zero_cohomologyZero :
    ∃ a : cohomologyZero p, a ≠ 0 ∧ p • a = 0 :=
  ⟨tauClass p, tauClass_ne_zero p, prime_smul_tauClass p⟩

/-- **Pulling back by Frobenius `F^* : H⁰(Cris(X/S), 𝒪_{X/S}) → H⁰(Cris(X/S), 𝒪_{X/S})` is not
injective**, for `X = Spec(𝐅_p[x, y]/(x², xy, y²))` and `S = Spec(ℤ_p)` with the divided power
ideal `(p)`. -/
@[stacks 07LJ "conclusion (2): pulling back by Frobenius F^* : H^0(Cris(X/S), O_{X/S}) → \
H^0(Cris(X/S), O_{X/S}) is not injective, for X = Spec(F_p[x, y]/(x^2, xy, y^2)) and \
S = Spec(ZZ_p) with the divided power ideal (p)"]
theorem not_injective_frobeniusPullback : ¬ Function.Injective (frobeniusPullback p) := by
  intro h
  exact tauClass_ne_zero p (h ((frobeniusPullback_tauClass p).trans (map_zero _).symm))

end TorsionExample

end Crystalline

end
