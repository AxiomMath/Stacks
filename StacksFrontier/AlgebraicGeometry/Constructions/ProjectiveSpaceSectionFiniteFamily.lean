module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic

/-!
# One hyperplane section for a whole finite family of modules on projective space

Let `ℱ_i` be finitely many `𝒪`-modules on `ℙⁿ_S` and let `s` be a global section of `𝒪(1)`.
Say that `s` *works* for a module `ℱ` when it satisfies the three conditions under which
[Stacks, Tag 08A0] states its short exact sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ ⟶ 0`,

namely that multiplication by `s` is a monomorphism, that its composite with the restriction to
the hyperplane `V(s)` vanishes, and that the unit of the pullback–pushforward adjunction is an
isomorphism at the cokernel. If a single `s` works for the direct sum `⨁ ℱ_i`, then that same `s`
works for each `ℱ_i`, and so the sequence of Tag 08A0 is short exact for every member of the
family at once.

## Main definitions

* `tensorMonoidal`: the tensor product sheaf as a monoidal structure on the `𝒪`-modules of
  `ℙⁿ_S`.
* `SectionWorksFor`: the three conditions under which [Stacks, Tag 08A0] states its sequence for
  a module and a section.

## Main results

* `twistSectionMulNegOne_naturality`: multiplication by a global section of `𝒪(1)`, as an arrow
  `ℱ(-1) ⟶ ℱ`, is natural in `ℱ`.
* `sectionWorksFor_of_retract`: the three conditions descend from a module to any retract of it.
* `exists_section_forall_shortExact`: a section of `𝒪(1)` that works for the direct sum of a
  finite family works for every member of it, so the sequence of [Stacks, Tag 08A0] is short
  exact for each of them.
* `exists_section_forall_shortExact_of_infiniteField`: the same over an infinite field `k` and
  for `n ≥ 1`.

## References

* [Stacks Project, Tag 08A1](https://stacks.math.columbia.edu/tag/08A1)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! ### Two retract arguments -/

/-- **A natural transformation out of the identity functor that is invertible at an object is
invertible at every retract of that object.** -/
private theorem isIso_app_of_retract {C : Type*} [Category C] {T : C ⥤ C} (η : 𝟭 C ⟶ T)
    {X Y : C} (p : X ⟶ Y) (q : Y ⟶ X) (hpq : p ≫ q = 𝟙 X) [IsIso (η.app Y)] :
    IsIso (η.app X) := by
  have hp : η.app X ≫ T.map p = p ≫ η.app Y := (η.naturality p).symm
  have hq : η.app Y ≫ T.map q = q ≫ η.app X := (η.naturality q).symm
  refine ⟨⟨T.map p ≫ inv (η.app Y) ≫ q, ?_, ?_⟩⟩
  · rw [← Category.assoc, hp, Category.assoc, IsIso.hom_inv_id_assoc, hpq]
    rfl
  · rw [Category.assoc, Category.assoc, ← hq, IsIso.inv_hom_id_assoc,
      ← CategoryTheory.Functor.map_comp, hpq, CategoryTheory.Functor.map_id]

/-- **The cokernel of a map is a retract of the cokernel of any map it is a retract of**, in the
category of arrows: a retraction of commuting squares induces a retraction of cokernels. -/
private theorem cokernel_map_comp_cokernel_map {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    [Limits.HasCokernel f] [Limits.HasCokernel g] (p : A ⟶ A') (q : B ⟶ B') (p' : A' ⟶ A)
    (q' : B' ⟶ B) (w : f ≫ q = p ≫ g) (w' : g ≫ q' = p' ≫ f) (hq : q ≫ q' = 𝟙 B) :
    Limits.cokernel.map f g p q w ≫ Limits.cokernel.map g f p' q' w' = 𝟙 _ := by
  refine (cancel_epi (Limits.cokernel.π f)).mp ?_
  rw [← Category.assoc, Limits.cokernel.π_desc, Category.assoc, Limits.cokernel.π_desc,
    ← Category.assoc, hq, Category.id_comp, Category.comp_id]

/-! ### Naturality of multiplication by a global section of `𝒪(1)` -/

variable (n : ℕ) (S : Scheme.{u})

/-- The tensor product sheaf as a monoidal structure on the `𝒪`-modules of `ℙⁿ_S`, with the unit
and associativity constraints that `twistSectionMul` is built from. -/
noncomputable abbrev tensorMonoidal :
    MonoidalCategory ((projectiveSpaceOver n S).Modules) :=
  Stacks.SheafOfModules.sheafTensorMonoidal (projectiveSpaceOver n S).presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n S))

attribute [local instance] tensorMonoidal

/-- A global section of an `𝒪`-module on `ℙⁿ_S`, read as a morphism out of the monoidal unit. -/
noncomputable abbrev unitSectionHom {F : (projectiveSpaceOver n S).Modules}
    (s : F.sections) : 𝟙_ ((projectiveSpaceOver n S).Modules) ⟶ F :=
  sectionHom F s

/-- The comparison `𝒪(-1 + 1) ⟶ 𝒪` of the degree `-1 + 1` twist with the monoidal unit. -/
private noncomputable abbrev twistNegOneSuccUnitHom :
    twistOver n S ((-1 : ℤ) + 1) ⟶ 𝟙_ ((projectiveSpaceOver n S).Modules) :=
  eqToHom (congrArg (twistOver n S) (show (-1 : ℤ) + 1 = 0 from by ring)) ≫
    (twistZeroIsoUnit n S).hom

/-- **Tensoring on the right with a morphism out of the structure sheaf is left whiskering**, in
`tensorMonoidal`. -/
theorem tensorRightOfUnitHom_eq_whiskerLeft (A : (projectiveSpaceOver n S).Modules)
    {B : (projectiveSpaceOver n S).Modules} (f : 𝟙_ ((projectiveSpaceOver n S).Modules) ⟶ B) :
    tensorRightOfUnitHom n S A f = A ◁ f :=
  tensorRightOfUnitHom_eq_map n S A f

/-- **Tensoring on the right with a morphism of modules is left whiskering**, in
`tensorMonoidal`. -/
theorem tensorRightOfHom_eq_whiskerLeft (A : (projectiveSpaceOver n S).Modules)
    {B C : (projectiveSpaceOver n S).Modules} (f : B ⟶ C) :
    tensorRightOfHom n S A f = A ◁ f :=
  tensorRightOfHom_eq_map n S A f

/-- **`twistSectionMul` in the monoidal vocabulary of `tensorMonoidal`**: multiplication by `s`
on `ℱ(d)` is the inverse right unitor, followed by whiskering with `s`, the associator, and
whiskering with the multiplication isomorphism `𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d + 1)`. -/
theorem twistSectionMul_eq_monoidal (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    twistSectionMul n S F s d =
      (ρ_ (F ⊗ twistOver n S d)).inv ≫
        (F ⊗ twistOver n S d) ◁ unitSectionHom n S s ≫
        (α_ F (twistOver n S d) (twistOver n S 1)).hom ≫
        F ◁ (twistOverMulIso n S d 1).hom := by
  rw [← tensorRightOfUnitHom_eq_whiskerLeft, ← tensorRightOfHom_eq_whiskerLeft]
  rfl

/-- **`twistSectionMulNegOne` in the monoidal vocabulary of `tensorMonoidal`**: it is
`twistSectionMul` at `d = -1`, followed by the trivialisation of `𝒪(-1 + 1)` and the right
unitor. -/
private theorem twistSectionMulNegOne_eq_monoidal (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    twistSectionMulNegOne n S F s =
      twistSectionMul n S F s (-1) ≫ F ◁ twistNegOneSuccUnitHom n S ≫ (ρ_ F).hom := by
  rw [← tensorRightOfHom_eq_whiskerLeft]
  rfl

/-- Multiplication by a global section `s` of `𝒪(1)` is natural in the module: the arrow
`ℱ(d) ⟶ ℱ(d + 1)` commutes with a morphism `ℱ ⟶ 𝒢` whiskered by the twists. -/
@[reassoc]
private theorem twistSectionMul_naturality {F G : (projectiveSpaceOver n S).Modules} (f : F ⟶ G)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    f ▷ twistOver n S d ≫ twistSectionMul n S G s d =
      twistSectionMul n S F s d ≫ f ▷ twistOver n S (d + 1) := by
  rw [twistSectionMul_eq_monoidal n S G s d, twistSectionMul_eq_monoidal n S F s d,
    rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, Category.assoc,
    Category.assoc, Category.assoc, associator_naturality_left_assoc, ← whisker_exchange]

/-- **Multiplication by a global section `s` of `𝒪(1)`, as the arrow `ℱ(-1) ⟶ ℱ`, is natural in
`ℱ`.** -/
@[reassoc]
theorem twistSectionMulNegOne_naturality {F G : (projectiveSpaceOver n S).Modules} (f : F ⟶ G)
    (s : (twistOver n S 1).sections) :
    f ▷ twistOver n S (-1) ≫ twistSectionMulNegOne n S G s =
      twistSectionMulNegOne n S F s ≫ f := by
  rw [twistSectionMulNegOne_eq_monoidal n S G s, twistSectionMulNegOne_eq_monoidal n S F s,
    twistSectionMul_naturality_assoc, Category.assoc, Category.assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

/-! ### A single section for a finite family -/

/-- **The three conditions under which [Stacks, Tag 08A0] states its sequence for a module `ℱ` on
`ℙⁿ_S` and a global section `s` of `𝒪(1)`**: multiplication by `s` is a monomorphism
`ℱ(-1) ⟶ ℱ`, its composite with the restriction to the hyperplane `V(s)` vanishes, and the unit
of the pullback–pushforward adjunction is an isomorphism at the cokernel. -/
def SectionWorksFor (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) : Prop :=
  Mono (twistSectionMulNegOne n S F s) ∧
    twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s = 0 ∧
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.app
      (Limits.cokernel (twistSectionMulNegOne n S F s)))

/-- **A global section of `𝒪(1)` that works for a module works for every retract of it.** If
`a : ℱ ⟶ 𝒢` has a retraction `b` and `s` satisfies the three conditions of [Stacks, Tag 08A0]
for `𝒢`, then it satisfies them for `ℱ`. -/
theorem sectionWorksFor_of_retract {F G : (projectiveSpaceOver n S).Modules} (a : F ⟶ G)
    (b : G ⟶ F) (hab : a ≫ b = 𝟙 F) (s : (twistOver n S 1).sections)
    (hG : SectionWorksFor n S G s) : SectionWorksFor n S F s := by
  obtain ⟨hmono, hzero, hiso⟩ := hG
  have hsm : IsSplitMono (a ▷ twistOver n S (-1)) :=
    ⟨⟨⟨b ▷ twistOver n S (-1), by rw [← comp_whiskerRight, hab, id_whiskerRight]⟩⟩⟩
  have hwF : twistSectionMulNegOne n S F s ≫ a =
      (a ▷ twistOver n S (-1)) ≫ twistSectionMulNegOne n S G s :=
    (twistSectionMulNegOne_naturality n S a s).symm
  have hwG : twistSectionMulNegOne n S G s ≫ b =
      (b ▷ twistOver n S (-1)) ≫ twistSectionMulNegOne n S F s :=
    (twistSectionMulNegOne_naturality n S b s).symm
  have hmonoF : Mono (twistSectionMulNegOne n S F s) := by
    have hc : Mono ((a ▷ twistOver n S (-1)) ≫ twistSectionMulNegOne n S G s) := mono_comp _ _
    rw [← hwF] at hc
    exact mono_of_mono _ a
  refine ⟨hmonoF, ?_, ?_⟩
  · have : IsSplitMono a := ⟨⟨⟨b, hab⟩⟩⟩
    have hnat : hyperplaneUnit n S F s ≫ (Scheme.Modules.pullback (hyperplaneι n S s) ⋙
        Scheme.Modules.pushforward (hyperplaneι n S s)).map a =
        a ≫ hyperplaneUnit n S G s :=
      ((Scheme.Modules.pullbackPushforwardAdjunction (hyperplaneι n S s)).unit.naturality a).symm
    have hcomp : (twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s) ≫
        (Scheme.Modules.pullback (hyperplaneι n S s) ⋙
          Scheme.Modules.pushforward (hyperplaneι n S s)).map a = 0 := by
      rw [Category.assoc, hnat, ← Category.assoc, hwF, Category.assoc, hzero, Limits.comp_zero]
    exact (cancel_mono _).mp (hcomp.trans Limits.zero_comp.symm)
  · have huv := cokernel_map_comp_cokernel_map (twistSectionMulNegOne n S F s)
      (twistSectionMulNegOne n S G s) (a ▷ twistOver n S (-1)) a (b ▷ twistOver n S (-1)) b
      hwF hwG hab
    exact isIso_app_of_retract _ _ _ huv

/-- **One global section of `𝒪(1)` for a whole finite family.** If `s` satisfies the three
conditions of [Stacks, Tag 08A0] for the direct sum of a finite family of `𝒪`-modules on `ℙⁿ_S`,
then the short exact sequence of that lemma exists for every member of the family, with this
single `s`. -/
theorem exists_section_forall_shortExact {ι : Type*} [Finite ι]
    (F : ι → (projectiveSpaceOver n S).Modules)
    (h : ∃ s : (twistOver n S 1).sections, SectionWorksFor n S (⨁ F) s) :
    ∃ s : (twistOver n S 1).sections, ∀ i : ι,
      ∃ hz : twistSectionMulNegOne n S (F i) s ≫ hyperplaneUnit n S (F i) s = 0,
        (ShortComplex.mk (twistSectionMulNegOne n S (F i) s) (hyperplaneUnit n S (F i) s)
          hz).ShortExact := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun i => ?_⟩
  obtain ⟨hmono, hzero, hiso⟩ :=
    sectionWorksFor_of_retract n S (Limits.biproduct.ι F i) (Limits.biproduct.π F i)
      (Limits.biproduct.ι_π_self F i) s hs
  exact shortExact_hyperplaneUnit n S (F i) s hzero hiso

/-- **One global section of `𝒪(1)` works for a finite family of modules on `ℙⁿ_k`.** Over an
infinite field `k` and for `n ≥ 1`, if a section `s` satisfies the three conditions of
[Stacks, Tag 08A0] for the direct sum of a finite family of `𝒪`-modules, then the short exact
sequence of that lemma exists for every member of the family, with this single `s`. -/
-- Implementation note: do not register `@[stacks 08A1]` here, since this statement assumes its
-- input on the direct sum; the tag is registered on `exists_section_forall_shortExact_coherent`.
theorem exists_section_forall_shortExact_of_infiniteField {k : Type u} [Field k] [Infinite k]
    (_hn : 1 ≤ n) {ι : Type*} [Finite ι]
    (F : ι → (projectiveSpaceOver n (Spec (CommRingCat.of k))).Modules)
    (h : ∃ s : (twistOver n (Spec (CommRingCat.of k)) 1).sections,
      SectionWorksFor n (Spec (CommRingCat.of k)) (⨁ F) s) :
    ∃ s : (twistOver n (Spec (CommRingCat.of k)) 1).sections, ∀ i : ι,
      ∃ hz : twistSectionMulNegOne n (Spec (CommRingCat.of k)) (F i) s ≫
          hyperplaneUnit n (Spec (CommRingCat.of k)) (F i) s = 0,
        (ShortComplex.mk (twistSectionMulNegOne n (Spec (CommRingCat.of k)) (F i) s)
          (hyperplaneUnit n (Spec (CommRingCat.of k)) (F i) s) hz).ShortExact :=
  exists_section_forall_shortExact n (Spec (CommRingCat.of k)) F h

end Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily

end
