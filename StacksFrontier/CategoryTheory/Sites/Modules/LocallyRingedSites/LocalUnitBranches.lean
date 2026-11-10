module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.LocalUnitConditions
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local-unit map of a sheaf of rings

Condition (3) of Stacks 04ES asserts that a map of sheaves of sets
`(O × O) ⊔ (O × O) ⟶ O × O` is surjective, the two components sending `(f, a)` to `(f, a·f)`
and `(f, b)` to `(f, b·(1 - f))`. This file builds those two components out of the pointwise
ring operations `CategoryTheory.Sheaf.ringMulHom`, `.ringAddHom`, `.ringNegHom` and
`.ringOneHom` of the underlying sheaf of sets of a sheaf of rings, and identifies their joint
surjectivity with the sectionwise condition `Stacks.Sheaves.LocallyRingedSite.Condition3`.

The two components are kept as a pair of parallel morphisms rather than as a single morphism
out of a coproduct, because what the inverse image along a morphism of topoi preserves with no
further hypothesis is *joint* epimorphy: a left adjoint carries a jointly epimorphic pair to a
jointly epimorphic pair. The coproduct is needed only to connect joint epimorphy with local
surjectivity.

## Main definitions

* `Stacks.Sheaves.LocalRingedness.JointlyEpi`: two parallel morphisms are jointly epimorphic.
* `Stacks.Sheaves.LocalRingedness.oneSubFst`: the morphism `(f, c) ↦ 1 - f`.
* `Stacks.Sheaves.LocalRingedness.localUnitBranch`: the component `(f, a) ↦ (f, a·f)` of the
  local-unit map for `b = false`, and `(f, a) ↦ (f, a·(1 - f))` for `b = true`.

## Main results

* `Stacks.Sheaves.LocalRingedness.jointlyEpi_localUnitBranch_iff_isLocallySurjective`: joint
  epimorphy of the two components is surjectivity of the map out of their coproduct.
* `Stacks.Sheaves.LocalRingedness.jointlyEpi_localUnitBranch_iff_condition3`: joint epimorphy
  of the two components is condition (3) of Stacks 04ES.

## Implementation notes

Every `GrothendieckTopology.HasSheafCompose` hypothesis is taken as an instance argument rather
than derived, even where it is derivable: `CategoryTheory.Sheaf.ringSheaf` takes one before its
explicit argument, and synthesising it while the universe arguments are still unknown assigns
them `0`.

## References

* [Stacks Project, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.LocalRingedness

universe t s w v u

/-! ### Jointly epimorphic pairs -/

section JointlyEpi

variable {A : Type u} [Category.{v} A]

/-- A pair of parallel morphisms with common source and target is *jointly epimorphic* when the
two of them cancel on the right together: any two morphisms out of their common target which
agree after both are equal. -/
def JointlyEpi {P Q : A} (a b : P ⟶ Q) : Prop :=
  ∀ ⦃Z : A⦄ (g h : Q ⟶ Z), a ≫ g = a ≫ h → b ≫ g = b ≫ h → g = h

/-- A left adjoint carries a jointly epimorphic pair to a jointly epimorphic pair. -/
lemma JointlyEpi.map {B : Type s} [Category.{t} B] {P Q : A} {a b : P ⟶ Q}
    (h : JointlyEpi a b) {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) :
    JointlyEpi (F.map a) (F.map b) := by
  intro Z g k hg hk
  refine (adj.homEquiv Q Z).injective (h _ _ ?_ ?_) <;>
    simp only [← adj.homEquiv_naturality_left, hg, hk]

/-- A faithful functor reflects joint epimorphy. -/
lemma JointlyEpi.of_map {B : Type s} [Category.{t} B] {P Q : A} {a b : P ⟶ Q} (F : A ⥤ B)
    [F.Faithful] (h : JointlyEpi (F.map a) (F.map b)) : JointlyEpi a b := by
  intro Z g k hg hk
  refine F.map_injective (h _ _ ?_ ?_) <;> simp only [← F.map_comp, hg, hk]

/-- Joint epimorphy transfers along an isomorphism of the common target, given a morphism of
the common source making both squares commute. -/
lemma JointlyEpi.conj {P P' Q Q' : A} {a b : P ⟶ Q} {a' b' : P' ⟶ Q'} {k : P ⟶ P'}
    (h : JointlyEpi a b) (eQ : Q ≅ Q')
    (ha : a ≫ eQ.hom = k ≫ a') (hb : b ≫ eQ.hom = k ≫ b') :
    JointlyEpi a' b' := by
  intro Z g m hg hm
  refine (cancel_epi eQ.hom).mp (h _ _ ?_ ?_) <;>
    simp only [reassoc_of% ha, reassoc_of% hb, hg, hm]

end JointlyEpi

/-! ### The two components of the local-unit map -/

section Branches

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] (R : Sheaf J RingCat.{w})

-- Mathlib's instance deriving `HasBinaryProduct (G.obj X) (G.obj Y)` from a preserved
-- product sends the search for `ringSheaf R ⨯ ringSheaf R` into `Sheaf J RingCat`, where it
-- times out.
attribute [-instance]
  CategoryTheory.Limits.instHasBinaryProductObjOfPreservesLimitDiscreteWalkingPairPair

/-- The square of the underlying sheaf of sets of a sheaf of rings. -/
noncomputable abbrev ringSq : Sheaf J (Type w) := Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R

/-- The morphism `(f, c) ↦ 1 - f` out of the square of the underlying sheaf of sets of a sheaf
of rings. -/
noncomputable def oneSubFst : ringSq R ⟶ Sheaf.ringSheaf R :=
  prod.lift (terminal.from _ ≫ Sheaf.ringOneHom R) (prod.fst ≫ Sheaf.ringNegHom R) ≫
    Sheaf.ringAddHom R

@[simp]
lemma sectionsFunctor_map_oneSubFst (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor.{w} J X).obj (ringSq R)) :
    (Sheaf.sectionsFunctor.{w} J X).map (oneSubFst R) z =
      1 - (Sheaf.sectionsFunctor.{w} J X).map prod.fst z := by
  rw [oneSubFst, Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_comp_apply,
    Functor.map_terminalFrom_apply, Sheaf.sectionsFunctor_map_ringAddHom,
    Sheaf.sectionsFunctor_map_ringOneHom, Functor.map_comp_apply,
    Sheaf.sectionsFunctor_map_ringNegHom, sub_eq_add_neg]

/-- The multiplier used by the component `b` of the local-unit map: the first projection for
`b = false`, and `1 -` the first projection for `b = true`. -/
noncomputable def localUnitFactor (b : Bool) : ringSq R ⟶ Sheaf.ringSheaf R :=
  if b then oneSubFst R else prod.fst

@[simp]
lemma sectionsFunctor_map_localUnitFactor (b : Bool) (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor.{w} J X).obj (ringSq R)) :
    (Sheaf.sectionsFunctor.{w} J X).map (localUnitFactor R b) z =
      (if b then 1 - (Sheaf.sectionsFunctor.{w} J X).map prod.fst z
        else (Sheaf.sectionsFunctor.{w} J X).map prod.fst z) := by
  cases b with
  | false => simp only [localUnitFactor, Bool.false_eq_true, ite_false]
  | true => simp only [localUnitFactor, ite_true, sectionsFunctor_map_oneSubFst]

/-- **Stacks 04ES, Definition 3.** A component of the local-unit map of a sheaf of rings: it
takes a pair of sections `(f, a)` to `(f, a·f)` for `b = false`, and to `(f, a·(1 - f))` for
`b = true`. -/
noncomputable def localUnitBranch (b : Bool) : ringSq R ⟶ ringSq R :=
  prod.lift prod.fst (prod.lift prod.snd (localUnitFactor R b) ≫ Sheaf.ringMulHom R)

@[simp]
lemma sectionsFunctor_map_localUnitBranch (b : Bool) (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor.{w} J X).obj (ringSq R)) :
    (Sheaf.sectionsFunctor.{w} J X).map (localUnitBranch R b) z =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} J X)
        ((Sheaf.sectionsFunctor.{w} J X).map prod.fst z)
        ((Sheaf.sectionsFunctor.{w} J X).map prod.snd z *
          (if b then 1 - (Sheaf.sectionsFunctor.{w} J X).map prod.fst z
            else (Sheaf.sectionsFunctor.{w} J X).map prod.fst z)) := by
  rw [localUnitBranch, Functor.map_lift_apply, Functor.map_comp_apply, Functor.map_lift_apply,
    Sheaf.sectionsFunctor_map_ringMulHom, sectionsFunctor_map_localUnitFactor]

/-- The first projection is unchanged by every component of the local-unit map. -/
lemma localUnitBranch_comp_fst (b : Bool) : localUnitBranch R b ≫ prod.fst = prod.fst := by
  rw [localUnitBranch, prod.lift_fst]

end Branches

/-! ### Joint epimorphy and local surjectivity -/

/-- Coproducts indexed by `ULift Bool` in sheaves of sets, supplied by name.

`HasFiniteCoproducts (Sheaf J (Type u))` is found by instance search at once, but the step from
it to a single discrete shape — Mathlib's
`CategoryTheory.Limits.hasColimitsOfShape_discrete` — is not reached inside the default
heartbeat budget, so the coproduct in `localUnitDesc` below has to be given its instance rather
than left to search. -/
@[sga "3 IV 4.4.1" "(ii), special case",
  sga "4 II 4.1" "Clause 2, special case",
  sga "4 II 4.8" "b), special case",
  sga "4 IV 1.1.2" "b), special case"]
local instance hasColimitsOfShape_discrete_uliftBool {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} :
    HasColimitsOfShape (Discrete (ULift.{u} Bool)) (Sheaf J (Type u)) :=
  hasColimitsOfShape_discrete (Sheaf J (Type u)) (ULift.{u} Bool)

section Desc

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{u})] (R : Sheaf J RingCat.{u})

/-- The local-unit map of Stacks 04ES, Definition 3, as a single morphism out of the coproduct
of two copies of the square of the underlying sheaf of sets. -/
noncomputable def localUnitDesc : (∐ fun _ : ULift.{u} Bool ↦ ringSq R) ⟶ ringSq R :=
  Sigma.desc fun i ↦ localUnitBranch R i.down

lemma sigmaι_comp_localUnitDesc (i : ULift.{u} Bool) :
    Sigma.ι (fun _ : ULift.{u} Bool ↦ ringSq R) i ≫ localUnitDesc R =
      localUnitBranch R i.down :=
  colimit.ι_desc _ _

/-- Joint epimorphy of the two components of the local-unit map is surjectivity of the map out
of their coproduct. -/
lemma jointlyEpi_localUnitBranch_iff_isLocallySurjective :
    JointlyEpi (localUnitBranch R false) (localUnitBranch R true) ↔
      Sheaf.IsLocallySurjective (localUnitDesc R) := by
  rw [Sheaf.isLocallySurjective_iff_epi (localUnitDesc R)]
  constructor
  · intro h
    refine ⟨fun g k hgk ↦ h g k ?_ ?_⟩
    · rw [← sigmaι_comp_localUnitDesc R ⟨false⟩, Category.assoc, Category.assoc, hgk]
    · rw [← sigmaι_comp_localUnitDesc R ⟨true⟩, Category.assoc, Category.assoc, hgk]
  · intro h _ g k hg hk
    refine (cancel_epi (localUnitDesc R)).mp (Sigma.hom_ext _ _ fun i ↦ ?_)
    rw [← Category.assoc, ← Category.assoc, sigmaι_comp_localUnitDesc]
    obtain ⟨b⟩ := i
    cases b with
    | false => exact hg
    | true => exact hk

end Desc

/-! ### The sectionwise form of joint epimorphy -/

section Condition

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{u})] (O : Sheaf J CommRingCat.{u})

/-- A section of the square of the structure sheaf is in the image of some component of the
local-unit map exactly when its second coordinate restricts to a multiple of the restriction of
its first, or of the complement of the restriction of its first. -/
private lemma exists_localUnitBranch_eq_iff {U V : C} (g : V ⟶ U)
    (s : (Sheaf.sectionsFunctor J (op U)).obj (ringSq (SheafOfModules.Tensor.ringSheaf O))) :
    (∃ (b : Bool) (t : (Sheaf.sectionsFunctor J (op V)).obj
          (ringSq (SheafOfModules.Tensor.ringSheaf O))),
        (Sheaf.sectionsFunctor J (op V)).map
            (localUnitBranch (SheafOfModules.Tensor.ringSheaf O) b) t =
          (Sheaf.sectionsRestrict (J := J) g.op).app
            (ringSq (SheafOfModules.Tensor.ringSheaf O)) s) ↔
      ∃ (b : Bool) (a : (Sheaf.sectionsFunctor J (op V)).obj
          (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))),
        (Sheaf.sectionsRestrict (J := J) g.op).app
            (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
            ((Sheaf.sectionsFunctor J (op U)).map prod.snd s) =
          a * (if b then
                1 - (Sheaf.sectionsRestrict (J := J) g.op).app
                  (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
                  ((Sheaf.sectionsFunctor J (op U)).map prod.fst s)
              else
                (Sheaf.sectionsRestrict (J := J) g.op).app
                  (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
                  ((Sheaf.sectionsFunctor J (op U)).map prod.fst s)) := by
  have hfst := Functor.natTrans_app_map_apply (Sheaf.sectionsRestrict (J := J) g.op)
    (prod.fst (X := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      (Y := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))) s
  have hsnd := Functor.natTrans_app_map_apply (Sheaf.sectionsRestrict (J := J) g.op)
    (prod.snd (X := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      (Y := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))) s
  constructor
  · rintro ⟨b, t, ht⟩
    rw [sectionsFunctor_map_localUnitBranch] at ht
    have h₁ := congrArg ((Sheaf.sectionsFunctor J (op V)).map prod.fst) ht
    have h₂ := congrArg ((Sheaf.sectionsFunctor J (op V)).map prod.snd) ht
    rw [Functor.map_fst_prodObjMk, ← hfst] at h₁
    rw [Functor.map_snd_prodObjMk, ← hsnd] at h₂
    exact ⟨b, (Sheaf.sectionsFunctor J (op V)).map prod.snd t, by rw [← h₂, h₁]⟩
  · rintro ⟨b, a, ha⟩
    refine ⟨b, Functor.prodObjMk (P := Sheaf.sectionsFunctor J (op V))
      (A := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      (B := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      ((Sheaf.sectionsRestrict (J := J) g.op).app
        (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
        ((Sheaf.sectionsFunctor J (op U)).map prod.fst s)) a, ?_⟩
    rw [sectionsFunctor_map_localUnitBranch, Functor.map_fst_prodObjMk,
      Functor.map_snd_prodObjMk, ← ha, hfst, hsnd, Functor.prodObjMk_map_fst_map_snd]

/-- The pair `(f, c)` of sections of the structure sheaf is, after restriction along `g`, in the
image of one of the two components of the local-unit map exactly when the predicate of condition
(3) of Stacks 04ES holds for it at `g`. -/
private lemma exists_localUnitBranch_prodObjMk_iff {U V : C} (g : V ⟶ U)
    (f c : Stacks.Sheaves.LocallyRingedSite.sections O U) :
    (∃ (b : Bool) (t : (Sheaf.sectionsFunctor J (op V)).obj
          (ringSq (SheafOfModules.Tensor.ringSheaf O))),
        (Sheaf.sectionsFunctor J (op V)).map
            (localUnitBranch (SheafOfModules.Tensor.ringSheaf O) b) t =
          (Sheaf.sectionsRestrict (J := J) g.op).app (ringSq (SheafOfModules.Tensor.ringSheaf O))
            (Functor.prodObjMk (P := Sheaf.sectionsFunctor J (op U))
              (A := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
              (B := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)) f c)) ↔
      ((∃ a : Stacks.Sheaves.LocallyRingedSite.sections O V,
          Stacks.Sheaves.LocallyRingedSite.restrict O g c = a *
            Stacks.Sheaves.LocallyRingedSite.restrict O g f) ∨
        ∃ b : Stacks.Sheaves.LocallyRingedSite.sections O V,
          Stacks.Sheaves.LocallyRingedSite.restrict O g c = b *
            Stacks.Sheaves.LocallyRingedSite.restrict O g (1 - f)) := by
  have hone : Stacks.Sheaves.LocallyRingedSite.restrict O g (1 - f) = 1 -
    Stacks.Sheaves.LocallyRingedSite.restrict O g f := by
    rw [Stacks.Sheaves.LocallyRingedSite.restrict_sub,
      Stacks.Sheaves.LocallyRingedSite.restrict_one]
  rw [exists_localUnitBranch_eq_iff O g, hone,
    Functor.map_fst_prodObjMk (P := Sheaf.sectionsFunctor J (op U))
      (A := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      (B := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)) f c,
    Functor.map_snd_prodObjMk (P := Sheaf.sectionsFunctor J (op U))
      (A := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      (B := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)) f c]
  constructor
  · rintro ⟨b, a, ha⟩
    cases b with
    | false => exact Or.inl ⟨a, ha⟩
    | true => exact Or.inr ⟨a, ha⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨false, a, ha⟩
    · exact ⟨true, a, ha⟩

/-- **Stacks 04ES.** Joint epimorphy of the two components of the local-unit map of a sheaf of
commutative rings is condition (3) of the source. -/
theorem jointlyEpi_localUnitBranch_iff_condition3 :
    JointlyEpi (localUnitBranch (SheafOfModules.Tensor.ringSheaf O) false)
        (localUnitBranch (SheafOfModules.Tensor.ringSheaf O) true) ↔
      Stacks.Sheaves.LocallyRingedSite.Condition3 O := by
  rw [jointlyEpi_localUnitBranch_iff_isLocallySurjective, localUnitDesc,
    Sheaf.isLocallySurjective_sigmaDesc_iff]
  constructor
  · intro h U f c
    obtain ⟨T, hT, hcov⟩ :=
      h (U := U) (Functor.prodObjMk (P := Sheaf.sectionsFunctor J (op U))
        (A := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
        (B := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)) f c)
    refine ⟨T, hT, fun V g hg ↦ ?_⟩
    obtain ⟨i, t, ht⟩ := hcov g hg
    exact (exists_localUnitBranch_prodObjMk_iff O g f c).1 ⟨i.down, t, ht⟩
  · intro h U s
    obtain ⟨T, hT, hcov⟩ := h U ((Sheaf.sectionsFunctor J (op U)).map prod.fst s)
      ((Sheaf.sectionsFunctor J (op U)).map prod.snd s)
    refine ⟨T, hT, fun V g hg ↦ ?_⟩
    obtain ⟨b, t, ht⟩ := (exists_localUnitBranch_prodObjMk_iff O g _ _).2 (hcov g hg)
    rw [Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J (op U))
      (A := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))
      (B := Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)) s] at ht
    exact ⟨ULift.up b, t, ht⟩

end Condition

end Stacks.Sheaves.LocalRingedness

end
