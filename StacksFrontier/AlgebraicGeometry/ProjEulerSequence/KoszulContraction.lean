module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSectionwiseDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk
public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul contraction on the exterior powers of a sheaf of modules

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it, `F` a sheaf of `O♯`-modules and
`φ : F ⟶ O♯` a morphism into the unit sheaf of modules. Stacks Tag 062K attaches to `φ` the
*Koszul complex* of `F`: the exterior algebra `⋀(F)` equipped with the degree `-1` derivation `d`
whose value on a degree-one local section `e` is the scalar `φ(e)`. This file **constructs that
derivation**, degreewise, as morphisms of sheaves of modules

`ι_φ : ⋀^{n+1} F ⟶ ⋀ⁿ F`,

for an arbitrary exterior algebra of `F` in the sense of Stacks Section 17.21, and proves that on
a wedge of local sections it is the alternating sum

`ι_φ(s₀ ∧ ⋯ ∧ sₙ) = ∑ₖ (-1)ᵏ φ(sₖ) · (s₀ ∧ ⋯ ∧ ŝₖ ∧ ⋯ ∧ sₙ)`,

whose degree-one case is the defining equation `d(e) = φ(e)` of Tag 062K. The derivation squares
to zero.

The construction is sectionwise and goes through three things that are already available. Over a
single object `X` of the site the sections of `F` form an honest module over the ring `O♯(X)`, so
`φ` is a *sectionwise functional* on `F` in the sense of
`PresheafOfModules.SectionwiseDual`, and the Koszul differential of that functional on the
presheaf of sectionwise exterior powers is `PresheafOfModules.SectionwiseDual.extPowKoszulD`.
Sheafifying degreewise gives the differential on the sheafified sectionwise exterior algebra, and
`SheafOfModules.exteriorPieceIso` — the degreewise comparison of that algebra with any exterior
algebra of `F`, which exists because both are universal for square-zero degree-one generators —
transports it to the exterior powers of the given algebra. Nothing about the comparison beyond
its being an isomorphism is used, so the contraction exists for *every* exterior algebra of `F`
and in particular for the chosen package `SheafOfModules.algebras`.

## Main definitions

* `SheafOfModules.unitDualApp` and `SheafOfModules.unitDual`: **the sectionwise functional of a
  morphism `φ : F ⟶ O♯`**, the datum the sectionwise Koszul differential consumes.
  `SheafOfModules.unitDualCommApp` is the same functional with its scalars spelled at the sheaf
  of commutative rings.
* `SheafOfModules.sectionwiseExteriorContraction`: the contraction on the homogeneous pieces of
  the sheafified sectionwise exterior algebra, i.e. the sheafification of `extPowKoszulD`.
* `SheafOfModules.exteriorContraction`: **the Koszul contraction `⋀^{n+1} F ⟶ ⋀ⁿ F`** on the
  exterior powers of an arbitrary exterior algebra of `F`.

## Main results

* `exteriorPower.contraction_eq_koszulD`: **the two module-level contractions of this library are
  the same map.** `exteriorPower.contraction`, built from
  `AlternatingMap.alternatizeUncurryFin`, and `Koszul.d`, the restriction of
  `CliffordAlgebra.contractLeft` to exterior powers, agree.
* `SheafOfModules.extPowKoszulD_app_commRing`: the sectionwise differential read over the ring of
  sections of the sheaf of commutative rings rather than of the underlying sheaf of rings.
* `SheafOfModules.extPowCmp_app_exteriorContraction`: **the contraction is the sectionwise Koszul
  differential, read through the comparison morphism of Tag 01CG.** This is the equation that
  pins it down, that morphism being a local epimorphism onto the exterior power.
* `SheafOfModules.extPowCmp_app_exteriorContraction_ιMulti`: **the alternating-sum formula on a
  wedge of local sections**, and `extPowCmp_app_exteriorContraction_one`: its degree-one case,
  which is the defining equation `d(e) = φ(e)` of Tag 062K.
* `SheafOfModules.extPowKoszulD_comp_extPowKoszulD` and
  `SheafOfModules.exteriorContraction_comp_exteriorContraction`: **the contraction squares to
  zero**, sectionwise and after sheafification.
* `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_extPowCmp` and
  `SheafOfModules.exists_stalkMapL_extPowCmp_eq`: on a topological space, the comparison
  isomorphism of Tag 01CH evaluated on the image of the comparison morphism of Tag 01CG is the
  stalk comparison of the presheaf of sectionwise exterior powers, and every germ of an exterior
  power is such an image.

## Implementation notes

What is forced and what is chosen.

* **The contraction is defined through the sheafified sectionwise algebra, not through the
  universal property.** A derivation is not a homomorphism of graded algebras, so
  `SheafOfModules.GradedAlgebra.IsExteriorAlgebra` cannot produce it directly: the classical
  route through the universal property maps `⋀(F)` into an algebra of endomorphisms of `⋀(F)`
  with a sign-twisted multiplication, which this development does not have for sheaves of
  modules. The sectionwise route needs nothing new, because over an object of the site the
  exterior power is an honest exterior power of an honest module.
* **No degree transport appears.** The degree-`k` piece of the sheafified sectionwise exterior
  algebra is the sheafification of `PresheafOfModules.extPow k` by definition — the `ℤ`-extended
  family `Stacks.GradedAlgebra.extendFamily` matches on the *constructors* of `ℤ`, so at
  `Int.ofNat k` it is that presheaf on the nose — so `sectionwiseExteriorContraction` is the
  sheafification functor applied to a morphism and nothing else. This is why the degrees below
  are natural numbers cast to `ℤ` and not integers: the successor is where the contraction lives,
  and `⋀^0 F` is the structure sheaf, where it is zero.
* **Two spellings of the ring of sections, and where the passage between them is paid for.** The
  sections of `O♯` over `X` carry a `CommRing` instance as a `CommRingCat` object and a second
  one, not syntactically equal to it, as an object of `RingCat` through
  `forget₂ CommRingCat RingCat`. An exterior power formed over one is not an exterior power
  formed over the other for unification, and `ExteriorAlgebra` is a Clifford quotient, so
  comparing the two exhausts the heartbeat budget wherever it happens. The sectionwise algebras
  are written at the `RingCat` spelling and the stalk comparisons at the `CommRingCat` one;
  `SheafOfModules.unitDualCommApp` and `SheafOfModules.extPowKoszulD_app_commRing` are the
  bridge, and the latter is `rfl` precisely so that the comparison happens once, in a
  declaration that does nothing else. Everything else in the file stays on one side.
* **The equations are stated on sections, not as equalities of morphisms.** The two spellings of
  a section of a presheaf of modules — `(P n).obj X` and `((toPresheaf R).obj (P n)).obj X` —
  are the same type with `AddCommMonoid` instances that are not syntactically equal, and a
  rewrite inside a goal mixing them is refused as not type-correct at `implicit` transparency.
  The proofs below are therefore `Eq.trans` and `congrArg` chains, which are checked at full
  transparency; the same obstruction is recorded in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSheafifiedDifferential`.
* **What is not here: the stalk of the contraction.** `exteriorPower.contraction_eq_koszulD` and
  the two stalk lemmas above are the two ends of the identity
  `(⋀ⁿ ι_φ)ₓ = exteriorPower.contraction ψ n` under the comparison of Tag 01CH, for a functional
  `ψ` on the stalk whose value on a germ is the germ of the value of `φ`; the middle step, that
  `PresheafOfModules.extPowStalkEquiv` intertwines `extPowKoszulD` with `Koszul.d ψ`, is not
  proved. Its natural proof — base change along the germ maps, which is
  `PresheafOfModules.extPowStalkL_germ`, followed by `Koszul.mapₛₗ_contraction` — mixes the two
  ring spellings of the previous note in a single `ExteriorAlgebra`, and does not elaborate
  inside the heartbeat limit. The spelling-free route is
  `PresheafOfModules.extPowStalkL_germ_ιMulti`, whose statement stays at the `RingCat` spelling,
  together with a span argument over `exteriorPower.ιMulti_span_fixedDegree` reducing an
  arbitrary germ to a germ of a wedge of local sections.
* **Universes.** In the site part the site universes `v`, `u` and the ring universe `w` are
  independent, as in `SheafOfModules.TensorExteriorSymmetricAlgebras`; the module universe is `w`
  as well, which `PresheafOfModules.extPow` forces. In
  `exteriorPower.contraction_eq_koszulD` the ring and the module share a universe, which is
  inherited from `Stacks.RegularSequence.koszulD_ιMulti`; the stalk part is in a single universe,
  which `TopCat.Presheaf.stalk` forces. Nothing is narrowed.
* **No `@[stacks]` attribute.** Tag 062K is the *definition* of the Koszul complex, which
  presupposes the existence and uniqueness of the derivation and proves neither; what is proved
  here is existence, with the defining equation, and not uniqueness or the
  differential-graded-algebra presentation, so the covering set of the tag is not complete and
  placing it here is a judgement for the integrator.
  `Stacks.RegularSequence.KoszulChainData`, which carries the same derivation as a hypothesis
  because it was not available, is not discharged here either; see the previous note.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace
open scoped ExteriorAlgebra

universe v u w

/-! ### The two spellings of the module-level contraction -/

namespace exteriorPower

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- **The two contractions of this library agree.** `exteriorPower.contraction φ n`, built from
`AlternatingMap.alternatizeUncurryFin`, and `Koszul.d φ n`, the restriction to exterior powers of
`CliffordAlgebra.contractLeft`, are the same linear map `⋀^{n+1} M →ₗ[R] ⋀ⁿ M`: both send a wedge
`m₀ ∧ ⋯ ∧ mₙ` to the alternating sum `∑ i, (-1)ⁱ φ(mᵢ) · (m₀ ∧ ⋯ ∧ m̂ᵢ ∧ ⋯ ∧ mₙ)`. -/
theorem contraction_eq_koszulD (φ : Module.Dual R M) (n : ℕ) :
    contraction φ n = Koszul.d φ n := by
  refine linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply]
  rw [contraction_ιMulti, Stacks.RegularSequence.koszulD_ιMulti]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ (i : ℕ)), smul_smul]
  push_cast
  rfl

end exteriorPower

/-! ### The sectionwise functional of a morphism into the unit sheaf of modules -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  {M : SheafOfModules.{w} (toRingCat J Osharp)}

/-- The scalar a morphism into the unit sheaf of modules attaches to a local section, as a
functional on the sections over one object of the site.

This is a `def` with an ascribed result type rather than a type ascription: the sections of
`SheafOfModules.unit (toRingCat J Osharp)` over `X` and the ring `O♯(X)` are the same type, but
instance search does not unfold the former, so a type ascription would leave the value unusable
as a scalar. -/
noncomputable def unitDualApp (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) (X : Cᵒᵖ) :
    Module.Dual ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (M.val.obj X) :=
  (φ.val.app X).hom

/-- The functional `unitDualApp φ X` sends a section `m` over `X` to `φ(X)(m)`. -/
theorem unitDualApp_apply (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) (X : Cᵒᵖ)
    (m : M.val.obj X) : unitDualApp φ X m = φ.val.app X m := rfl

/-- **The sectionwise functional of a morphism `φ : F ⟶ 𝒪_X` of sheaves of modules.** This is the
`PresheafOfModules.SectionwiseDual` given by the `O♯(X)`-linear functional
`φ(X) : F(X) ⟶ O♯(X)` over every object `X`, together with its compatibility with restriction,
which is the naturality of `φ`. -/
noncomputable def unitDual (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) :
    PresheafOfModules.SectionwiseDual.{v, u, w, w} M.val where
  app X := unitDualApp φ X
  naturality f m := (PresheafOfModules.naturality_apply φ.val f m).symm

/-- The component of `unitDual φ` over `X` sends a section `m` over `X` to `φ(X)(m)`. -/
theorem unitDual_app_apply (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) (X : Cᵒᵖ)
    (m : M.val.obj X) : (unitDual φ).app X m = φ.val.app X m := rfl

/-- `SheafOfModules.unitDualApp` with its scalars spelled at the sheaf of *commutative* rings
rather than at the underlying sheaf of rings.

The two spellings of the ring of sections are the same type carrying `CommRing` instances which
are not syntactically equal, so an exterior power formed over one of them is not an exterior
power formed over the other as far as unification is concerned. `PresheafOfModules.germₛₗ`, and
with it the whole stalk comparison of the sectionwise exterior powers, is written at the
commutative spelling; this declaration and
`SheafOfModules.extPowKoszulD_app_commRing` below are where the passage between the two is
paid for, once. -/
noncomputable def unitDualCommApp (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) (X : Cᵒᵖ) :
    Module.Dual ↑(Osharp.obj.obj X) (M.val.obj X) :=
  (φ.val.app X).hom

/-- The sectionwise Koszul differential is `Koszul.d` of the functional, with the exterior powers
spelled over the ring of sections of the sheaf of commutative rings. Both sides are the same
term; the content is that the two `CommRing` instances agree, and this is the one declaration in
which that is checked. -/
theorem extPowKoszulD_app_commRing (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp))
    (n : ℕ) (X : Cᵒᵖ) (y : (PresheafOfModules.extPow (n + 1) M.val).obj X) :
    ((((unitDual φ).extPowKoszulD n).app X y : ⋀[↑(Osharp.obj.obj X)]^n (M.val.obj X))) =
      Koszul.d (unitDualCommApp φ X) n y := rfl

/-! ### The contraction -/

/-- The sectionwise Koszul differential squares to zero already on the presheaves of sectionwise
exterior powers, because contraction does. -/
theorem extPowKoszulD_comp_extPowKoszulD
    (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) (n : ℕ) :
    (unitDual φ).extPowKoszulD (n + 1) ≫ (unitDual φ).extPowKoszulD n = 0 := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Subtype.ext ?_
  refine Eq.trans ((unitDual φ).extPowKoszulDApp_coe n X _) ?_
  refine Eq.trans (congrArg (Koszul.contraction ((unitDual φ).app X))
    ((unitDual φ).extPowKoszulDApp_coe (n + 1) X x)) ?_
  exact CliffordAlgebra.contractLeft_contractLeft ((unitDual φ).app X) _

section Contraction

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

variable (M)

/-- **The Koszul contraction on the sheafified sectionwise exterior powers**: the sheafification
of `PresheafOfModules.SectionwiseDual.extPowKoszulD`, a morphism `⋀^{n+1} F ⟶ ⋀ⁿ F` of the
homogeneous pieces of the sheafified sectionwise exterior algebra.

No degree transport occurs: the degree-`k` piece of that algebra is the sheafification of the
presheaf of sectionwise `k`-th exterior powers by definition, the `ℤ`-extended family being
given by a match on the constructors of `ℤ`. -/
@[sga "7 XII 1.3.1" "more general"]
noncomputable def sectionwiseExteriorContraction
    (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp)) (n : ℕ) :
    (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).piece ((n + 1 : ℕ) : ℤ) ⟶
      (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) M.val).piece ((n : ℕ) : ℤ) :=
  (PresheafOfModules.sheafification (toRingCatMap J (𝟙 Osharp.obj))).map
    ((unitDual φ).extPowKoszulD n)

variable (A : GradedAlgebra.{w, w} (toRingCat J Osharp)) (gen : M ⟶ A.piece 1)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen)
  (φ : M ⟶ SheafOfModules.unit (toRingCat J Osharp))

/-- **The Koszul contraction on the exterior powers of a sheaf of modules.** For a morphism
`φ : F ⟶ 𝒪` into the unit sheaf of modules and an exterior algebra `A` of `F` in the sense of
Stacks Section 17.21, this is the degree-lowering morphism

`⋀^{n+1} F ⟶ ⋀ⁿ F`

of sheaves of modules which on a local section `s₀ ∧ ⋯ ∧ sₙ` is the alternating sum
`∑ i, (-1)ⁱ φ(sᵢ) · (s₀ ∧ ⋯ ∧ ŝᵢ ∧ ⋯ ∧ sₙ)`.

It is the sheafified sectionwise contraction, transported along
`SheafOfModules.exteriorPieceIso`, the degreewise comparison of the sheafified sectionwise
exterior algebra with `A`. -/
noncomputable def exteriorContraction (n : ℕ) :
    A.piece ((n + 1 : ℕ) : ℤ) ⟶ A.piece ((n : ℕ) : ℤ) :=
  (exteriorPieceIso M A gen hA ((n + 1 : ℕ) : ℤ)).inv ≫
    sectionwiseExteriorContraction M φ n ≫ (exteriorPieceIso M A gen hA ((n : ℕ) : ℤ)).hom

/-- **The contraction is the sectionwise Koszul differential, read through the comparison
morphism of Tag 01CG.** This is the equation that pins the contraction down: the comparison
morphism `extPowCmp` is a local epimorphism onto the exterior power, so no other morphism has
this property. -/
theorem extPowCmp_app_exteriorContraction (n : ℕ) (X : Cᵒᵖ)
    (x : (PresheafOfModules.extPow (n + 1) M.val).obj X) :
    (exteriorContraction M A gen hA φ n).val.app X
        ((A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 (n + 1)).app X x) =
      (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 n).app X
        (((unitDual φ).extPowKoszulD n).app X x) := by
  have hcmp : ∀ (k : ℕ) (y : (PresheafOfModules.extPow k M.val).obj X),
      (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 k).app X y =
        (exteriorPieceIso M A gen hA (k : ℤ)).hom.val.app X
          (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (toRingCatMap J (𝟙 Osharp.obj)) (PresheafOfModules.extPow k M.val)) X y) :=
    fun k y => PresheafOfModules.hom_congr_apply
      (extPowCmp_eq_sheafifyUnit_comp M A gen hA.1 hA k) X y
  rw [hcmp, hcmp]
  exact congrArg (fun z => (exteriorPieceIso M A gen hA ((n : ℕ) : ℤ)).hom.val.app X z)
    (Eq.trans (congrArg (fun z => (sectionwiseExteriorContraction M φ n).val.app X z)
      (iso_inv_hom_app_apply (exteriorPieceIso M A gen hA ((n + 1 : ℕ) : ℤ)) X _))
      (PresheafOfModules.unit_naturality_apply ((unitDual φ).extPowKoszulD n) X x))

/-- **The contraction on a wedge of local sections is the alternating sum**
`∑ k, (-1)^k φ(s k) · (s₀ ∧ ⋯ ∧ ŝₖ ∧ ⋯ ∧ sₙ)`.

This is the degree `-1` derivation property of Stacks Tag 062K made explicit: it is the value of
the differential on an exterior monomial, and it determines the contraction, wedges of local
sections generating the exterior power locally. -/
theorem extPowCmp_app_exteriorContraction_ιMulti (n : ℕ) (X : Cᵒᵖ)
    (s : Fin (n + 1) → M.val.obj X) :
    (exteriorContraction M A gen hA φ n).val.app X
        ((A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 (n + 1)).app X
          (exteriorPower.ιMulti
            ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (n + 1) s)) =
      (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 n).app X
        (∑ k : Fin (n + 1),
          ((-1 : (Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) ^ (k : ℕ) *
              unitDualApp φ X (s k)) •
            exteriorPower.ιMulti
              ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) n
              fun j => s (k.succAbove j)) := by
  refine Eq.trans (extPowCmp_app_exteriorContraction M A gen hA φ n X _) ?_
  exact congrArg
    (fun z => (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 n).app X z)
    (Stacks.RegularSequence.koszulD_ιMulti ((unitDual φ).app X) n s)

/-- **The defining property of Stacks Tag 062K**: on a degree-one local section the contraction
is the scalar `φ(s)`, read in degree zero. This is the case `n = 0` of
`SheafOfModules.extPowCmp_app_exteriorContraction_ιMulti`. -/
theorem extPowCmp_app_exteriorContraction_one (X : Cᵒᵖ) (s : M.val.obj X) :
    (exteriorContraction M A gen hA φ 0).val.app X
        ((A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 1).app X
          (exteriorPower.ιMulti
            ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) 1 fun _ => s)) =
      (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 0).app X
        (unitDualApp φ X s •
          exteriorPower.ιMulti
            ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) 0 fun _ => s) := by
  refine Eq.trans (extPowCmp_app_exteriorContraction_ιMulti M A gen hA φ 0 X fun _ => s) ?_
  refine congrArg
    (fun z => (A.extPowCmp (hO := (toRingCat J Osharp).property) gen hA.1 0).app X z) ?_
  refine Eq.trans (Fin.sum_univ_one _) ?_
  rw [Fin.val_zero, pow_zero, one_mul]

/-- **The contraction squares to zero**, because contraction of the exterior algebra does. -/
theorem exteriorContraction_comp_exteriorContraction (n : ℕ) :
    exteriorContraction M A gen hA φ (n + 1) ≫ exteriorContraction M A gen hA φ n = 0 := by
  have hzero : (PresheafOfModules.sheafification (toRingCatMap J (𝟙 Osharp.obj))).map
      ((unitDual φ).extPowKoszulD (n + 1) ≫ (unitDual φ).extPowKoszulD n) = 0 :=
    Eq.trans (congrArg (fun f => (PresheafOfModules.sheafification
        (toRingCatMap J (𝟙 Osharp.obj))).map f) (extPowKoszulD_comp_extPowKoszulD φ n))
      (Functor.map_zero _ _ _)
  have hsq : sectionwiseExteriorContraction M φ (n + 1) ≫ sectionwiseExteriorContraction M φ n
      = 0 :=
    Eq.trans ((PresheafOfModules.sheafification (toRingCatMap J (𝟙 Osharp.obj))).map_comp
      ((unitDual φ).extPowKoszulD (n + 1)) ((unitDual φ).extPowKoszulD n)).symm hzero
  rw [exteriorContraction, exteriorContraction, Category.assoc, Category.assoc,
    ← Category.assoc (exteriorPieceIso M A gen hA ((n + 1 : ℕ) : ℤ)).hom _ _,
    (exteriorPieceIso M A gen hA ((n + 1 : ℕ) : ℤ)).hom_inv_id, Category.id_comp,
    ← Category.assoc (sectionwiseExteriorContraction M φ (n + 1)) _ _, hsq, Limits.zero_comp,
    Limits.comp_zero]

end Contraction

end SheafOfModules

/-! ### The contraction at a stalk -/

namespace SheafOfModules

section Stalk

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsExteriorAlgebra A gen)
  (φ : M ⟶ SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

/-- The comparison isomorphism of Tag 01CH, read on the image of the comparison morphism of Tag
01CG, is the stalk comparison of the presheaf of sectionwise exterior powers. This is how a
computation on the presheaf is transported to the exterior power of the sheaf. -/
theorem exteriorPowerStalkEquiv_stalkMapL_extPowCmp (n : ℕ) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.extPow n M.val).presheaf x)) :
    exteriorPowerStalkEquiv A gen hA n x
        (PresheafOfModules.stalkMapL x
          (A.extPowCmp
            (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1 n) z) =
      PresheafOfModules.extPowStalkEquiv M.val x n z :=
  congrArg (PresheafOfModules.extPowStalkEquiv M.val x n)
    ((PresheafOfModules.stalkLinearEquiv x
      (A.extPowCmp
        (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1 n)
      (isIso_stalkFunctor_map_extPowCmp A gen hA n x)).symm_apply_apply z)

/-- Every germ of the degree-`n` exterior power comes from a germ of the presheaf of sectionwise
exterior powers, the comparison morphism of Tag 01CG being a stalk isomorphism. -/
theorem exists_stalkMapL_extPowCmp_eq (n : ℕ) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk (A.piece ((n : ℕ) : ℤ)).val.presheaf x)) :
    ∃ z, PresheafOfModules.stalkMapL x
      (A.extPowCmp
        (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1 n) z = t :=
  (PresheafOfModules.stalkLinearEquiv x
    (A.extPowCmp
      (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1 n)
    (isIso_stalkFunctor_map_extPowCmp A gen hA n x)).surjective t

end Stalk

end SheafOfModules

end
