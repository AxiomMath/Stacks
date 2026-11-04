module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.FppfAndSyntomic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology

/-!
# First cohomology of the roots of unity and pairs with trivial invertible sheaf

Let `S` be a scheme, `n` a natural number, and fix a site over `S` — the big fppf, big
syntomic, big étale or small étale site — on which the Kummer sequence
`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` of abelian sheaves is short exact. A global unit `a` on `S` is a
global section of `𝐆_m`, and the fibre of the `n`th power map over it — the sheaf of `n`th roots
of `a` — is a torsor under `μ_n`; its class in `H¹(S, μ_n)` is the boundary `∂a`. This file
constructs `∂`, shows that it is a homomorphism of abelian groups, and computes its fibres: `∂a`
and `∂b` agree exactly when `a` and `b` differ by the `n`th power of a global unit.

By `AlgebraicGeometry.pairIso_unitPair_iff` that is exactly the condition for the pairs
`(𝒪_S, a)` and `(𝒪_S, b)` of Tag 040Q to be isomorphic. So `∂` is the canonical injective
homomorphism from the group of isomorphism classes of pairs whose invertible sheaf is trivial —
the global units modulo `n`th powers — into `H¹(S, μ_n)`, and it carries such a pair to the
class of its torsor of trivializations. This is the part of Tag 040Q that concerns pairs with a
trivial invertible sheaf; see the implementation notes for what is not covered.

## Main definitions

* `AlgebraicGeometry.terminalFamily` and `AlgebraicGeometry.terminalSectionMorphism` present a
  section over a terminal object of a site as a morphism from the constant presheaf of integers.
* `AlgebraicGeometry.terminalBoundary` is the boundary, in the first cohomology of the kernel
  sheaf, of a global section of the quotient sheaf of a short exact sequence of abelian sheaves.
* `AlgebraicGeometry.unitsSection` is a global unit read as a section of the sheaf of units.
* `AlgebraicGeometry.kummerBoundary` and `AlgebraicGeometry.kummerBoundaryHom` are that boundary
  for the Kummer sequence, as a function of a global unit and as a homomorphism of abelian
  groups.

## Main results

* `AlgebraicGeometry.terminalBoundary_add`: the boundary map is additive.
* `AlgebraicGeometry.terminalBoundary_eq_zero_iff`: its kernel consists of the sections that
  lift to a global section of the middle sheaf.
* `AlgebraicGeometry.terminalBoundary_eq_fiberTorsorClass`: the boundary of a section is the
  class, under the bijection of Tag 03AJ, of the torsor given by the fibre over it.
* `AlgebraicGeometry.kummerBoundary_eq_zero_iff` and
  `AlgebraicGeometry.kummerBoundary_eq_iff`: the Kummer boundary of a global unit vanishes
  exactly when the unit is an `n`th power, and two global units have the same boundary exactly
  when they differ by an `n`th power.
* `AlgebraicGeometry.pairIso_iff_kummerBoundary_eq`: **Tag 040Q for the pairs with trivial
  invertible sheaf.** Two such pairs are isomorphic exactly when their cohomology classes agree.
* `AlgebraicGeometry.pairIso_iff_kummerBoundary_eq_fppf`,
  `AlgebraicGeometry.pairIso_iff_kummerBoundary_eq_syntomic`,
  `AlgebraicGeometry.pairIso_iff_kummerBoundary_eq_bigEtale` and
  `AlgebraicGeometry.pairIso_iff_kummerBoundary_eq_smallEtale` discharge the two hypotheses of
  that statement on the four sites: short exactness of the Kummer sequence comes from Tags 040N
  and 03PL, with `n` invertible on `S` in the étale cases, and the terminal object is `S / S`.

## Implementation notes

The boundary map is the one of Tag 03AJ: a global section of the quotient sheaf is a morphism
from the constant presheaf of integers, and the boundary is the composition of its class in
degree zero with the extension class of the sequence. Over a terminal object of the site such a
morphism is the same thing as a single section, which is what turns the lifting criterion
`Stacks.Cohomology.Torsors.boundary_eq_zero_iff_presheaf_lift` into the statement that a unit is
globally an `n`th power. Additivity is proved by following the construction: the presentation of
a section as a morphism, the sheafification bijection, and `Abelian.Ext.mk₀` are each additive.

What this file does **not** prove, and what Tag 040Q asserts beyond it: that every class in
`H¹(S, μ_n)` comes from a pair, and that pairs with a nontrivial invertible sheaf have classes
at all. Both need the sheaf of trivializations of a pair `(L, α)` with `L` nontrivial, that is,
the pullback of an invertible sheaf and of its trivialization along the objects of the site;
the library has no pullback of the tensor-power trivialization, so there is no map from the
full group of pairs to `H¹`. The group structure on the pairs with trivial invertible sheaf is
the one on the global units, not an abstract tensor product of pairs: the tensor product of
pairs is not constructed here either.

## References

* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.Torsors

namespace AlgebraicGeometry

universe w t v u

/-- On a scheme, multiplication on the sections of the structure sheaf is commutative. The
tensor-power API of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic` is
elaborated against this instance, which is `local` there and so has to be named again here. -/
local instance structureSections_isMulCommutative (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

section Boundary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The compatible family of restrictions of a section over a terminal object of a site. -/
def terminalFamily (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (x : A.obj (op T)) (U : Cᵒᵖ) : A.obj U :=
  A.map (hT.from U.unop).op x

/-- Restricting a section over a terminal object commutes with every restriction map. -/
theorem terminalFamily_naturality (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (x : A.obj (op T)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    A.map f (terminalFamily A hT x U) = terminalFamily A hT x V := by
  have h : (hT.from U.unop).op ≫ f = (hT.from V.unop).op :=
    Quiver.Hom.unop_inj (hT.hom_ext _ _)
  calc A.map f (terminalFamily A hT x U)
      = (A.map (hT.from U.unop).op ≫ A.map f) x := (ConcreteCategory.comp_apply _ _ x).symm
    _ = A.map ((hT.from U.unop).op ≫ f) x := by rw [A.map_comp]
    _ = terminalFamily A hT x V := by rw [h]; rfl

/-- The family of restrictions of a section over a terminal object is that section there. -/
theorem terminalFamily_terminal (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (x : A.obj (op T)) : terminalFamily A hT x (op T) = x := by
  have h : (hT.from T).op = 𝟙 (op T) := Quiver.Hom.unop_inj (hT.hom_ext _ _)
  show A.map (hT.from T).op x = x
  rw [h, A.map_id]
  rfl

/-- The morphism from the constant presheaf of integers determined by a section over a
terminal object. -/
def terminalSectionMorphism (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (x : A.obj (op T)) :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A :=
  morphismOfSectionFamily A (terminalFamily A hT x) (terminalFamily_naturality A hT x)

/-- The morphism determined by a section over a terminal object sends `1` over `U` to the
restriction of that section to `U`. -/
theorem terminalSectionMorphism_one (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (x : A.obj (op T)) (U : Cᵒᵖ) :
    (terminalSectionMorphism A hT x).app U ⟨1⟩ = terminalFamily A hT x U :=
  morphismOfSectionFamily_one A _ _ U

/-- A morphism from the constant presheaf of integers is determined by its value at `1`. -/
theorem constInt_hom_ext {A : Cᵒᵖ ⥤ AddCommGrpCat.{t}}
    (r r' : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A)
    (h : ∀ U, r.app U ⟨1⟩ = r'.app U ⟨1⟩) : r = r' :=
  NatTrans.ext (funext fun U => liftedInt_hom_ext _ _ (h U))

/-- The morphism determined by a section over a terminal object is additive in the section. -/
theorem terminalSectionMorphism_add (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (x y : A.obj (op T)) :
    terminalSectionMorphism A hT (x + y) =
      terminalSectionMorphism A hT x + terminalSectionMorphism A hT y := by
  refine constInt_hom_ext _ _ fun U => ?_
  rw [terminalSectionMorphism_one]
  show A.map _ (x + y) = _
  rw [map_add]
  show _ = (terminalSectionMorphism A hT x).app U ⟨1⟩ +
    (terminalSectionMorphism A hT y).app U ⟨1⟩
  rw [terminalSectionMorphism_one, terminalSectionMorphism_one]
  rfl

variable [HasSheafify J AddCommGrpCat.{t}]

/-- The adjunction bijection of sheafification is additive. -/
theorem sheafifyHomEquiv_add {P : Cᵒᵖ ⥤ AddCommGrpCat.{t}} {Y : Sheaf J AddCommGrpCat.{t}}
    (a b : (presheafToSheaf J AddCommGrpCat).obj P ⟶ Y) :
    (sheafificationAdjunction J AddCommGrpCat).homEquiv P Y (a + b) =
      (sheafificationAdjunction J AddCommGrpCat).homEquiv P Y a +
        (sheafificationAdjunction J AddCommGrpCat).homEquiv P Y b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    show ((sheafToPresheaf J AddCommGrpCat.{t}).map (a + b)) =
      (sheafToPresheaf J AddCommGrpCat.{t}).map a +
        (sheafToPresheaf J AddCommGrpCat.{t}).map b from rfl,
    Preadditive.comp_add]

/-- The inverse adjunction bijection of sheafification is additive. -/
theorem sheafifyHomEquiv_symm_add {P : Cᵒᵖ ⥤ AddCommGrpCat.{t}} {Y : Sheaf J AddCommGrpCat.{t}}
    (q q' : P ⟶ Y.obj) :
    ((sheafificationAdjunction J AddCommGrpCat).homEquiv P Y).symm (q + q') =
      ((sheafificationAdjunction J AddCommGrpCat).homEquiv P Y).symm q +
        ((sheafificationAdjunction J AddCommGrpCat).homEquiv P Y).symm q' := by
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv P Y).injective
  rw [Equiv.apply_symm_apply, sheafifyHomEquiv_add, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- The boundary, in first cohomology of the kernel sheaf, of a global section of the quotient
sheaf of a short exact sequence of abelian sheaves. -/
def terminalBoundary (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (x : S.X₃.obj.obj (op T)) : Sheaf.H S.X₁ 1 :=
  (Abelian.Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm
    (terminalSectionMorphism S.X₃.obj hT x))).comp hS.extClass (zero_add 1)

/-- The boundary spelled out, with the composition's degree equation given explicitly. -/
theorem terminalBoundary_eq (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (x : S.X₃.obj.obj (op T)) :
    terminalBoundary S hS hT x =
      (Abelian.Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat).homEquiv
          ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))) S.X₃).symm
          (terminalSectionMorphism S.X₃.obj hT x))).comp hS.extClass (zero_add 1) :=
  rfl

/-- The boundary map is a homomorphism of abelian groups. -/
theorem terminalBoundary_add (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    {T : C} (hT : IsTerminal T) (x y : S.X₃.obj.obj (op T)) :
    terminalBoundary S hS hT (x + y) =
      terminalBoundary S hS hT x + terminalBoundary S hS hT y := by
  rw [terminalBoundary_eq, terminalBoundary_eq, terminalBoundary_eq,
    terminalSectionMorphism_add, sheafifyHomEquiv_symm_add, Abelian.Ext.mk₀_add]
  exact Abelian.Ext.add_comp _ _ _ _

/-- **The boundary of a global section vanishes exactly when the section lifts globally.**
Over a terminal object of the site, a morphism out of the constant presheaf of integers is the
same thing as a section, so the lifting criterion in first cohomology becomes the existence of
a single global section of the middle sheaf above the given one. -/
theorem terminalBoundary_eq_zero_iff (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (hS : S.ShortExact) {T : C} (hT : IsTerminal T) (x : S.X₃.obj.obj (op T)) :
    terminalBoundary S hS hT x = 0 ↔
      ∃ y : S.X₂.obj.obj (op T), S.g.hom.app (op T) y = x := by
  refine Iff.trans (boundary_eq_zero_iff_presheaf_lift S hS
    (terminalSectionMorphism S.X₃.obj hT x)) ?_
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r.app (op T) ⟨1⟩, ?_⟩
    have h := congrArg (fun α => α.app (op T) (⟨1⟩ : ULift.{t} ℤ)) hr
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    rw [h, terminalSectionMorphism_one, terminalFamily_terminal]
  · rintro ⟨y, hy⟩
    refine ⟨terminalSectionMorphism S.X₂.obj hT y, ?_⟩
    refine constInt_hom_ext _ _ fun U => ?_
    show S.g.hom.app U ((terminalSectionMorphism S.X₂.obj hT y).app U ⟨1⟩) = _
    rw [terminalSectionMorphism_one, terminalSectionMorphism_one, terminalFamily,
      terminalFamily, ← hy]
    exact NatTrans.naturality_apply S.g.hom (hT.from U.unop).op y

/-- **The boundary of a global section is the class of its fibre torsor.** This pins down the
boundary map: the fibre of the quotient map over the section is a torsor under the kernel
sheaf, and its first cohomology class is the boundary. -/
theorem terminalBoundary_eq_fiberTorsorClass (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (hS : S.ShortExact) {T : C} (hT : IsTerminal T) (x : S.X₃.obj.obj (op T)) :
    torsorIsoClassesEquivH1 S.X₁ (Quotient.mk (torsorSetoid S.X₁)
        (fiberTorsor S hS (terminalSectionMorphism S.X₃.obj hT x))) =
      terminalBoundary S hS hT x :=
  (torsorIsoClassesEquivH1_eq_boundary_iff S hS _ _).2
    ⟨fiberInclusion S _, (fiberInclusion_spec S hS _).1,
      (fiberInclusion_spec S hS _).2.1, (fiberInclusion_spec S hS _).2.2⟩

end Boundary

section Kummer

variable {C : Type v} [Category.{u} C]

/-- A global unit on the scheme attached to an object of the site, as a section of the sheaf of
units there. -/
def unitsSection (F : C ⥤ Scheme.{u}) (T : C)
    (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) : (unitsPresheaf F).obj (op T) :=
  Additive.ofMul a

/-- The second map of the Kummer complex is the `n`th power map on sections. -/
theorem kummerSequence_g_app (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hF : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ) (T : C)
    (a : (unitsPresheaf F).obj (op T)) :
    (kummerSequence J F hF n).g.hom.app (op T) a = n • a :=
  rfl

variable (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
  (hF : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- Over an object of the site, a section of the sheaf of units is an `n`th multiple exactly
when the corresponding global unit is an `n`th power. -/
theorem exists_nsmul_unitsSection_iff (F : C ⥤ Scheme.{u}) (n : ℕ) (T : C)
    (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    (∃ y : (unitsPresheaf F).obj (op T), n • y = unitsSection F T a) ↔
      ∃ b : (Scheme.Γ.obj (op (F.obj T)))ˣ, a = b ^ n := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_pow]
    exact hy.symm
  · rintro ⟨b, rfl⟩
    exact ⟨unitsSection F T b, (ofMul_pow n b).symm⟩

/-- **The Kummer boundary of a global unit vanishes exactly when that unit is globally an
`n`th power.** The site is assumed to have a terminal object, over which the sections of the
sheaf of units are the global units of the scheme attached to it. -/
@[sga "7 IX 9.4.3" "special case"]
theorem kummerTerminalBoundary_eq_zero_iff
    (hS : (kummerSequence J F hF n).ShortExact) {T : C} (hT : IsTerminal T)
    (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    terminalBoundary (kummerSequence J F hF n) hS hT (unitsSection F T a) = 0 ↔
      ∃ b : (Scheme.Γ.obj (op (F.obj T)))ˣ, a = b ^ n :=
  Iff.trans (terminalBoundary_eq_zero_iff (kummerSequence J F hF n) hS hT
    (unitsSection F T a)) (exists_nsmul_unitsSection_iff F n T a)

variable (hS : (kummerSequence J F hF n).ShortExact) {T : C} (hT : IsTerminal T)

/-- The first cohomology class of a global unit under the Kummer boundary map: the class of the
torsor of its `n`th roots. -/
def kummerBoundary (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    Sheaf.H (kummerSequence J F hF n).X₁ 1 :=
  terminalBoundary (kummerSequence J F hF n) hS hT (unitsSection F T a)

/-- **The Kummer boundary is a homomorphism** from the global units to first cohomology of the
roots of unity. -/
theorem kummerBoundary_mul (a b : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    kummerBoundary J F hF n hS hT (a * b) =
      kummerBoundary J F hF n hS hT a + kummerBoundary J F hF n hS hT b :=
  terminalBoundary_add (kummerSequence J F hF n) hS hT
    (unitsSection F T a) (unitsSection F T b)

/-- **The Kummer boundary of a global unit vanishes exactly when the unit is an `n`th power.**
-/
theorem kummerBoundary_eq_zero_iff (a : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    kummerBoundary J F hF n hS hT a = 0 ↔
      ∃ b : (Scheme.Γ.obj (op (F.obj T)))ˣ, a = b ^ n :=
  kummerTerminalBoundary_eq_zero_iff J F hF n hS hT a

/-- Splitting off a unit from the Kummer boundary. -/
theorem kummerBoundary_split (a b : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    kummerBoundary J F hF n hS hT a =
      kummerBoundary J F hF n hS hT (a * b⁻¹) + kummerBoundary J F hF n hS hT b :=
  (congrArg (kummerBoundary J F hF n hS hT) (inv_mul_cancel_right a b)).symm.trans
    (kummerBoundary_mul J F hF n hS hT (a * b⁻¹) b)

/-- **The Kummer boundary separates global units modulo `n`th powers.** -/
theorem kummerBoundary_eq_iff (a b : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    kummerBoundary J F hF n hS hT a = kummerBoundary J F hF n hS hT b ↔
      ∃ u : (Scheme.Γ.obj (op (F.obj T)))ˣ, a = u ^ n * b := by
  rw [kummerBoundary_split J F hF n hS hT a b, add_eq_right, kummerBoundary_eq_zero_iff]
  exact exists_congr fun u => mul_inv_eq_iff_eq_mul

/-- The Kummer boundary map as a homomorphism of abelian groups from the global units, written
additively, to the first cohomology of the sheaf of `n`th roots of unity. -/
@[sga "7 IX 9.4.3"]
def kummerBoundaryHom :
    Additive (Scheme.Γ.obj (op (F.obj T)))ˣ →+ Sheaf.H (kummerSequence J F hF n).X₁ 1 where
  toFun x := kummerBoundary J F hF n hS hT (Additive.toMul x)
  map_zero' := (kummerBoundary_eq_zero_iff J F hF n hS hT 1).2 ⟨1, (one_pow n).symm⟩
  map_add' x y := kummerBoundary_mul J F hF n hS hT (Additive.toMul x) (Additive.toMul y)

/-- **Stacks Project, Tag 040Q, for the pairs with trivial invertible sheaf.** Two pairs whose
invertible sheaf is the structure sheaf of the base are isomorphic as pairs exactly when they
have the same class in the first cohomology of the sheaf of `n`th roots of unity. Together with
`AlgebraicGeometry.kummerBoundary_mul` this is an injective homomorphism from the group of
isomorphism classes of such pairs — the global units modulo `n`th powers — into `H¹(S, μ_n)`,
and by `AlgebraicGeometry.terminalBoundary_eq_fiberTorsorClass` it carries a pair to the class
of its torsor of trivializations. -/
@[stacks 040Q "the pairs whose invertible sheaf is trivial: the canonical injective \
homomorphism from the global units modulo nth powers into H^1 of the roots of unity, carrying \
a pair to the class of its torsor of trivializations, on any site over the base having a \
terminal object and a short exact Kummer sequence (by 040N and 03PL: fppf, syntomic, and etale \
for n invertible on the base); pairs with a nontrivial invertible sheaf, and surjectivity onto \
H^1, are not covered", sga "7 IX 9.4.3" "special case"]
theorem pairIso_iff_kummerBoundary_eq (f g : (Scheme.Γ.obj (op (F.obj T)))ˣ) :
    Nonempty (PairIso (unitPair (F.obj T) n f) (unitPair (F.obj T) n g)) ↔
      kummerBoundary J F hF n hS hT f = kummerBoundary J F hF n hS hT g :=
  (pairIso_unitPair_iff (F.obj T) n f g).trans (kummerBoundary_eq_iff J F hF n hS hT f g).symm

end Kummer

section Sites

/-- **Stacks Project, Tag 040Q on the big fppf site.** The hypotheses of
`AlgebraicGeometry.pairIso_iff_kummerBoundary_eq` hold on the big fppf site over `S`, with no
assumption on `n` beyond positivity: the Kummer sequence is short exact there by Tag 040N, and
`S / S` is the terminal object. -/
@[stacks 040Q "the fppf case of the trivial-invertible-sheaf part, with the terminal object \
and the short exactness of the Kummer sequence discharged", sga "7 IX 9.4.3" "special case"]
theorem pairIso_iff_kummerBoundary_eq_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n)
    [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})]
    (f g : (Scheme.Γ.obj (op S))ˣ) :
    Nonempty (PairIso (unitPair S n f) (unitPair S n g)) ↔
      kummerBoundary (BigFppfOver.topology B S hS) (BigFppfOver.toScheme B S hS)
          (unitsPresheaf_isSheaf_fppf B S hS) n
          (kummerSequence_shortExact_fppf B S hS n hn)
          (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hS)))) f =
        kummerBoundary (BigFppfOver.topology B S hS) (BigFppfOver.toScheme B S hS)
          (unitsPresheaf_isSheaf_fppf B S hS) n
          (kummerSequence_shortExact_fppf B S hS n hn)
          (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hS)))) g :=
  pairIso_iff_kummerBoundary_eq (BigFppfOver.topology B S hS) (BigFppfOver.toScheme B S hS)
    (unitsPresheaf_isSheaf_fppf B S hS) n (kummerSequence_shortExact_fppf B S hS n hn)
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hS)))) f g

/-- **Stacks Project, Tag 040Q on the big syntomic site.** -/
@[stacks 040Q "the syntomic case of the trivial-invertible-sheaf part, with the terminal \
object and the short exactness of the Kummer sequence discharged"]
theorem pairIso_iff_kummerBoundary_eq_syntomic (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n)
    [HasSheafify (BigSyntomicOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigSyntomicOver.topology B S hS) AddCommGrpCat.{u})]
    (f g : (Scheme.Γ.obj (op S))ˣ) :
    Nonempty (PairIso (unitPair S n f) (unitPair S n g)) ↔
      kummerBoundary (BigSyntomicOver.topology B S hS) (BigSyntomicOver.toScheme B S hS)
          (unitsPresheaf_isSheaf_syntomic B S hS) n
          (kummerSequence_shortExact_syntomic B S hS n hn)
          (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))) f =
        kummerBoundary (BigSyntomicOver.topology B S hS) (BigSyntomicOver.toScheme B S hS)
          (unitsPresheaf_isSheaf_syntomic B S hS) n
          (kummerSequence_shortExact_syntomic B S hS n hn)
          (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))) g :=
  pairIso_iff_kummerBoundary_eq (BigSyntomicOver.topology B S hS)
    (BigSyntomicOver.toScheme B S hS) (unitsPresheaf_isSheaf_syntomic B S hS) n
    (kummerSequence_shortExact_syntomic B S hS n hn)
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))) f g

/-- **Stacks Project, Tag 040Q on the big étale site**, for `n` invertible on `S`. -/
@[stacks 040Q "the big etale case of the trivial-invertible-sheaf part, for n invertible on \
the base, with the terminal object and the short exactness of the Kummer sequence discharged"]
theorem pairIso_iff_kummerBoundary_eq_bigEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (op S)))
    [HasSheafify (BigEtaleOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigEtaleOver.topology B S hS) AddCommGrpCat.{u})]
    (f g : (Scheme.Γ.obj (op S))ˣ) :
    Nonempty (PairIso (unitPair S n f) (unitPair S n g)) ↔
      kummerBoundary (BigEtaleOver.topology B S hS) (BigEtaleOver.toScheme B S hS)
          (unitsPresheaf_isSheaf_bigEtale B S hS) n
          (kummerSequence_shortExact_bigEtale B S hS n hn)
          (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))) f =
        kummerBoundary (BigEtaleOver.topology B S hS) (BigEtaleOver.toScheme B S hS)
          (unitsPresheaf_isSheaf_bigEtale B S hS) n
          (kummerSequence_shortExact_bigEtale B S hS n hn)
          (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))) g :=
  pairIso_iff_kummerBoundary_eq (BigEtaleOver.topology B S hS) (BigEtaleOver.toScheme B S hS)
    (unitsPresheaf_isSheaf_bigEtale B S hS) n (kummerSequence_shortExact_bigEtale B S hS n hn)
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj S hS)))) f g

/-- **Stacks Project, Tag 040Q on the small étale site**, for `n` invertible on `S`. -/
@[stacks 040Q "the small etale case of the trivial-invertible-sheaf part, for n invertible on \
the base, with the terminal object and the short exactness of the Kummer sequence discharged"]
theorem pairIso_iff_kummerBoundary_eq_smallEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (op S)))
    [HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})]
    (f g : (Scheme.Γ.obj (op S))ˣ) :
    Nonempty (PairIso (unitPair S n f) (unitPair S n g)) ↔
      kummerBoundary (SmallEtale.topology B S hS) (SmallEtale.toScheme B S hS)
          (unitsPresheaf_isSheaf_smallEtale B S hS) n
          (kummerSequence_shortExact_smallEtale B S hS n hn)
          (SmallEtale.finalIsTerminal B S hS) f =
        kummerBoundary (SmallEtale.topology B S hS) (SmallEtale.toScheme B S hS)
          (unitsPresheaf_isSheaf_smallEtale B S hS) n
          (kummerSequence_shortExact_smallEtale B S hS n hn)
          (SmallEtale.finalIsTerminal B S hS) g :=
  pairIso_iff_kummerBoundary_eq (SmallEtale.topology B S hS) (SmallEtale.toScheme B S hS)
    (unitsPresheaf_isSheaf_smallEtale B S hS) n
    (kummerSequence_shortExact_smallEtale B S hS n hn)
    (SmallEtale.finalIsTerminal B S hS) f g

end Sites

end AlgebraicGeometry

end
