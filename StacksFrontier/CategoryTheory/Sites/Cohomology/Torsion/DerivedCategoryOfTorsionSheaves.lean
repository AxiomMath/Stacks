module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.QuasiIsoOfShortExact
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.CategoryTheory.Localization.HomEquiv
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.LocalImageSheaf

/-!
# The derived category of torsion abelian sheaves

Let `(C, J)` be a site. An abelian sheaf `F` on it is *torsion* when every section is locally
annihilated by a positive integer: for every object `U` and every `s ∈ F(U)` there is a
covering sieve of `U` such that for each of its members `V ⟶ U` some positive multiple of the
restriction of `s` to `V` vanishes. Stacks 0DD7 says that the torsion abelian sheaves form a
Serre subcategory, and that the derived category of that subcategory is equivalent to the full
subcategory of `D(Sh(J, Ab))` whose objects have torsion cohomology sheaves.

## Main definitions

* `Stacks.Torsion.torsionSheafProperty`: the property of being a torsion abelian sheaf.
* `Stacks.Torsion.TorsionSheaf`: the corresponding full subcategory.
* `Stacks.Torsion.torsionCohomologyProperty`: the property, for an object of the derived
  category, that all its cohomology sheaves are torsion.
* `Stacks.Torsion.TorsionDerivedCategory`: the corresponding full subcategory of the derived
  category.

## Main results

* `Stacks.Torsion.torsionSheafProperty_isSerreClass`: torsion abelian sheaves form a Serre
  subcategory.
* `Stacks.Torsion.exists_torsionDerivedEquivalence`: the derived equivalence, together with
  the compatibility that identifies its composition with the inclusion of the target
  subcategory with the derived functor of the inclusion of torsion sheaves.

## Implementation notes

Torsion is expressed intrinsically on a site: every section is *locally* killed by a positive
integer, with the integer allowed to vary over the members of the covering sieve. This is the
sheaf-theoretic torsion condition; unlike a uniform bound on a section it is stable under
quotients, which is what makes the class a Serre subcategory.

The equivalence is pinned down rather than merely asserted: the statement asks for an
equivalence whose functor, followed by the inclusion of the target full subcategory, is
naturally isomorphic to the derived functor of the inclusion of torsion sheaves. So it cannot
be satisfied by an unrelated equivalence of the two categories.

The torsion subsheaf is constructed by hand as the subpresheaf of locally torsion sections —
this is already a sheaf, no sheafification being needed — and `torsionSubsheafFunctor` is
shown to be right adjoint to the inclusion. That adjunction, transported to homotopy
categories, is what produces the replacements needed for the full faithfulness of the derived
functor on the localizations.

## References

* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Limits Opposite ZeroObject

universe w v u

open HomologicalComplex Opposite

private lemma quasiIso_unop_inverse {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex Aᵒᵖ ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((CochainComplex.opEquivalence A).inverse.map f).unop) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff' _ (i-1) i (i+1) (by simp) (by simp)]
  exact (ShortComplex.quasiIso_opMap_iff _).mp ((quasiIsoAt_iff' f (-(i+1)) (-i) (-(i-1))
    (by simp; omega) (by simp; omega)).mp (inferInstance : QuasiIsoAt f (-i)))

private lemma mono_nsmul_mappingCone {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (i : ℤ) (n : ℕ)
    [Mono (n • 𝟙 (K.X (i + 1)))] [Mono (n • 𝟙 (L.X i))] :
    Mono (n • 𝟙 ((CochainComplex.mappingCone f).X i)) := by
  apply Preadditive.mono_of_cancel_zero
  intro Z g hg
  have h₁ : g ≫ (CochainComplex.mappingCone.fst f).1.v i (i+1) rfl = 0 := by
    apply (cancel_mono (n • 𝟙 (K.X (i+1)))).mp
    simpa [Preadditive.comp_nsmul, Preadditive.nsmul_comp] using
      congrArg (fun t => t ≫ (CochainComplex.mappingCone.fst f).1.v i (i+1) rfl) hg
  have h₂ : g ≫ (CochainComplex.mappingCone.snd f).v i i (add_zero i) = 0 := by
    apply (cancel_mono (n • 𝟙 (L.X i))).mp
    simpa [Preadditive.comp_nsmul, Preadditive.nsmul_comp] using
      congrArg (fun t => t ≫ (CochainComplex.mappingCone.snd f).v i i (add_zero i)) hg
  rw [← Category.comp_id g, ← CochainComplex.mappingCone.id_X f i (i+1) rfl]
  simp [Preadditive.comp_add, ← Category.assoc, h₁, h₂]

private lemma exists_divisible_complex_replacement {A : Type*} [Category A] [Abelian A]
    {K D : CochainComplex A ℤ} (f : K ⟶ D) [Mono f]
    (hD : ∀ i (n : ℕ), 0 < n → Epi (n • 𝟙 (D.X i))) :
    ∃ (I : CochainComplex A ℤ) (g : K ⟶ I), QuasiIso g ∧
      ∀ i (n : ℕ), 0 < n → Epi (n • 𝟙 (I.X i)) := by
  let E := CochainComplex.opEquivalence A
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f) }
  let S' := S.op.map E.functor
  have : Mono S.op.f := hS.op.mono_f
  have : Epi S.op.g := hS.op.epi_g
  have hS' : S'.ShortExact := hS.op.map E.functor
  let M := CochainComplex.mappingCone S'.f
  let q := CochainComplex.mappingCone.descShortComplex S'
  have hq : QuasiIso q := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  let I := (E.inverse.obj M).unop
  let g : K ⟶ I := (E.unitIso.app (op K)).inv.unop ≫ (E.inverse.map q).unop
  refine ⟨I, g, ?_, ?_⟩
  · have : QuasiIso ((E.unitIso.app (op K)).inv.unop) := inferInstance
    exact quasiIso_comp (hφ' := quasiIso_unop_inverse q) _ _
  · intro i n hn
    have hQ (j : ℤ) : Epi (n • 𝟙 ((cokernel f).X j)) := by
      have := hD j n hn
      apply epi_of_epi_fac (f := (cokernel.π f).f j)
        (h := (n • 𝟙 (D.X j)) ≫ (cokernel.π f).f j)
      simp
    have h₁ : Mono (n • 𝟙 (S'.X₁.X (-i+1))) := by
      have := hQ (-(-i+1))
      show Mono ((n • 𝟙 ((cokernel f).X (-(-i+1)))).op)
      infer_instance
    have h₂ : Mono (n • 𝟙 (S'.X₂.X (-i))) := by
      have := hD (-(-i)) n hn
      show Mono ((n • 𝟙 (D.X (-(-i)))).op)
      infer_instance
    have := mono_nsmul_mappingCone S'.f (-i) n
    show Epi ((n • 𝟙 (M.X (-i))).unop)
    infer_instance

section LocalizedReplacements

variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Preadditive A] [Preadditive B] [Preadditive D] [Preadditive E]
  (W : MorphismProperty A) (V : MorphismProperty B)
  [W.HasLeftCalculusOfFractions] [V.HasLeftCalculusOfFractions]
  [V.HasTwoOutOfThreeProperty]
  (L : A ⥤ D) [L.IsLocalization W] [L.Additive]
  (M : B ⥤ E) [M.IsLocalization V] [M.Additive]
  (F : A ⥤ B) [F.Additive]

private lemma localized_homMap_eq_zero_of_replacements
    (hW : ∀ {X Y : A} (f : X ⟶ Y), W f ↔ V (F.map f))
    (hR : ∀ (Y : A) (Z : B) (s : F.obj Y ⟶ Z), V s →
      ∃ (Z' : B) (i : Z ⟶ Z') (R : A) (c : F.obj R ⟶ Z'),
        V i ∧ V c ∧ ∀ X : A,
          Function.Bijective (fun f : X ⟶ R => F.map f ≫ c))
    {X Y : A} (a : L.obj X ⟶ L.obj Y)
    (ha : (⟨F, fun _ _ f hf => (hW f).mp hf⟩ : LocalizerMorphism W V).homMap L M a = 0) :
    a = 0 := by
  let Φ : LocalizerMorphism W V := ⟨F, fun _ _ f hf => (hW f).mp hf⟩
  change Φ.homMap L M a = 0 at ha
  obtain ⟨z, rfl⟩ := Localization.exists_leftFraction L W a
  have hz : M.map (F.map z.f) = 0 := by
    have hz := congrArg (fun t => t ≫ M.map (F.map z.s)) ha
    rw [← Φ.homMap_map L M z.s, ← Φ.homMap_comp,
      MorphismProperty.LeftFraction.map_comp_map_s, Φ.homMap_map] at hz
    simpa using hz
  obtain ⟨Z, s, hs, hfs⟩ :=
    (MorphismProperty.map_eq_iff_postcomp M V (F.map z.f) 0).mp (by simpa using hz)
  obtain ⟨Z', i, R, c, hi, hc, hbij⟩ := hR z.Y' Z s hs
  obtain ⟨t, ht⟩ := (hbij z.Y').surjective (s ≫ i)
  dsimp only at ht
  have htW : W t := (hW t).mpr (by
    rw [← V.postcomp_iff _ _ hc, ht]
    exact V.comp_mem _ _ hs hi)
  have hft : z.f ≫ t = 0 := (hbij X).injective (by
    simp only [F.map_comp, Category.assoc, ht, F.map_zero, zero_comp]
    rw [← Category.assoc, hfs, zero_comp, zero_comp])
  have htIso : IsIso (L.map t) := Localization.inverts L W t htW
  have hf : L.map z.f = 0 := by
    apply (cancel_mono (L.map t)).mp
    simp [← L.map_comp, hft]
  simp [MorphismProperty.LeftFraction.map, hf]

omit [Preadditive A] [Preadditive B] [Preadditive D] [Preadditive E]
  [W.HasLeftCalculusOfFractions] [L.Additive] in
private lemma localized_homMap_surjective_of_replacements
    (hW : ∀ {X Y : A} (f : X ⟶ Y), W f ↔ V (F.map f))
    (hR : ∀ (Y : A) (Z : B) (s : F.obj Y ⟶ Z), V s →
      ∃ (Z' : B) (i : Z ⟶ Z') (R : A) (c : F.obj R ⟶ Z'),
        V i ∧ V c ∧ ∀ X : A,
          Function.Bijective (fun f : X ⟶ R => F.map f ≫ c))
    {X Y : A} (a : M.obj (F.obj X) ⟶ M.obj (F.obj Y)) :
    ∃ b : L.obj X ⟶ L.obj Y,
      (⟨F, fun _ _ f hf => (hW f).mp hf⟩ : LocalizerMorphism W V).homMap L M b = a := by
  let Φ : LocalizerMorphism W V := ⟨F, fun _ _ f hf => (hW f).mp hf⟩
  obtain ⟨z, rfl⟩ := Localization.exists_leftFraction M V a
  obtain ⟨Z', i, R, c, hi, hc, hbij⟩ := hR Y z.Y' z.s z.hs
  obtain ⟨f, hf⟩ := (hbij X).surjective (z.f ≫ i)
  obtain ⟨s, hs⟩ := (hbij Y).surjective (z.s ≫ i)
  dsimp only at hf hs
  have hsW : W s := (hW s).mpr (by
    rw [← V.postcomp_iff _ _ hc, hs]
    exact V.comp_mem _ _ z.hs hi)
  let b : W.LeftFraction X Y := ⟨f, s, hsW⟩
  refine ⟨b.map L (Localization.inverts L W), ?_⟩
  have hcIso : IsIso (M.map c) := Localization.inverts M V c hc
  have hsIso : IsIso (M.map (F.map s)) := Localization.inverts M V _ ((hW s).mp hsW)
  apply (cancel_mono (M.map (F.map s))).mp
  apply (cancel_mono (M.map c)).mp
  rw [← Φ.homMap_map L M s, ← Φ.homMap_comp,
    MorphismProperty.LeftFraction.map_comp_map_s, Φ.homMap_map]
  show M.map (F.map f) ≫ M.map c = _
  rw [← M.map_comp, hf, Φ.homMap_map, Category.assoc, ← M.map_comp, hs]
  simp only [M.map_comp, ← Category.assoc,
    MorphismProperty.LeftFraction.map_comp_map_s]

end LocalizedReplacements

private lemma localized_full_faithful_of_replacements
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive D] [Preadditive E]
    (W : MorphismProperty A) (V : MorphismProperty B)
    [W.HasLeftCalculusOfFractions] [V.HasLeftCalculusOfFractions]
    [V.HasTwoOutOfThreeProperty]
    (L : A ⥤ D) [L.IsLocalization W] [L.Additive]
    (M : B ⥤ E) [M.IsLocalization V] [M.Additive]
    (F : A ⥤ B) [F.Additive]
    (G : D ⥤ E) [G.Additive] (e : F ⋙ M ≅ L ⋙ G)
    (hW : ∀ {X Y : A} (f : X ⟶ Y), W f ↔ V (F.map f))
    (hR : ∀ (Y : A) (Z : B) (s : F.obj Y ⟶ Z), V s →
      ∃ (Z' : B) (i : Z ⟶ Z') (R : A) (c : F.obj R ⟶ Z'),
        V i ∧ V c ∧ ∀ X : A,
          Function.Bijective (fun f : X ⟶ R => F.map f ≫ c)) :
    G.Full ∧ G.Faithful := by
  let Φ : LocalizerMorphism W V := ⟨F, fun _ _ f hf => (hW f).mp hf⟩
  have : L.EssSurj := Localization.essSurj L W
  constructor
  · apply G.full_of_comp_essSurj L
    intro X Y a
    obtain ⟨b, hb⟩ := localized_homMap_surjective_of_replacements W V L M F hW hR
      (e.hom.app X ≫ a ≫ e.inv.app Y)
    refine ⟨b, ?_⟩
    change Φ.homMap L M b = _ at hb
    rw [Φ.homMap_apply L M G e] at hb
    exact (cancel_mono (e.inv.app Y)).mp ((cancel_epi (e.hom.app X)).mp hb)
  · apply G.faithful_of_comp_essSurj L
    intro X Y f g hfg
    apply sub_eq_zero.mp
    apply localized_homMap_eq_zero_of_replacements W V L M F hW hR
    show Φ.homMap L M _ = 0
    rw [Φ.homMap_apply L M G e, G.map_sub, hfg, sub_self]
    simp

private theorem homotopyCategory_quasiIso_hasTwoOutOfThreeProperty
    {A : Type*} [Category A] [Abelian A] :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg i := by
    let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i
    have : IsIso (H.map g) := hg i
    have : IsIso (H.map f ≫ H.map g) := by simpa only [Functor.map_comp] using hfg i
    exact IsIso.of_isIso_comp_right (H.map f) (H.map g)
  of_precomp f g hf hfg i := by
    let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i
    have : IsIso (H.map f) := hf i
    have : IsIso (H.map f ≫ H.map g) := by simpa only [Functor.map_comp] using hfg i
    exact IsIso.of_isIso_comp_left (H.map f) (H.map g)

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- Abelian sheaves on `J` form an abelian category. -/
local instance sheafAbelian : Abelian (Sheaf J AddCommGrpCat.{w}) :=
  CategoryTheory.sheafIsAbelian

section

attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- The property that an abelian sheaf is torsion: every local section is locally annihilated
by a positive integer. -/
@[sga "4 IX 1.1"]
public def torsionSheafProperty : ObjectProperty (Sheaf J AddCommGrpCat.{w}) :=
  fun F ↦ ∀ (U : C) (x : F.obj.obj (Opposite.op U)),
    ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f →
        ∃ n : ℕ, 0 < n ∧ n • (F.obj.map f.op x) = 0

end

/-- Torsion abelian sheaves on the site. -/
public abbrev TorsionSheaf := (torsionSheafProperty J).FullSubcategory

/- The torsion subsheaf is the sheafification of the pointwise torsion subgroup. -/
private def pointwiseTorsionSubfunctor (F : Sheaf J AddCommGrpCat.{w}) :
    Subfunctor (F.obj ⋙ forget AddCommGrpCat.{w}) where
  obj U := {x | ∃ n : ℕ, 0 < n ∧ n • x = 0}
  map {U V} f x hx := by
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n, hn, ?_⟩
    calc
      n • (F.obj.map f).hom' x = (F.obj.map f).hom' (n • x) := by
            rw [← _root_.map_nsmul]
            rfl
      _ = (F.obj.map f).hom' 0 := congrArg (F.obj.map f).hom' hnx
      _ = 0 := (F.obj.map f).hom'.map_zero

private def locallyTorsionSubfunctor (F : Sheaf J AddCommGrpCat.{w}) :
    Subfunctor (F.obj ⋙ forget AddCommGrpCat.{w}) :=
  (pointwiseTorsionSubfunctor J F).sheafify J

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem locallyTorsion_zero (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    (0 : F.obj.obj U) ∈ (locallyTorsionSubfunctor J F).obj U := by
  show (pointwiseTorsionSubfunctor J F).sieveOfSection 0 ∈ J U.unop
  apply J.superset_covering _ (J.top_mem U.unop)
  intro V i hi
  refine ⟨1, by omega, ?_⟩
  show 1 • (F.obj.map i.op).hom' (0 : F.obj.obj U) = 0
  rw [(F.obj.map i.op).hom'.map_zero]
  exact one_nsmul (0 : F.obj.obj (op V))

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem locallyTorsion_add (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ)
    (x y : F.obj.obj U) (hx : x ∈ (locallyTorsionSubfunctor J F).obj U)
    (hy : y ∈ (locallyTorsionSubfunctor J F).obj U) :
    x + y ∈ (locallyTorsionSubfunctor J F).obj U := by
  show (pointwiseTorsionSubfunctor J F).sieveOfSection (x + y) ∈ J U.unop
  change (pointwiseTorsionSubfunctor J F).sieveOfSection x ∈ J U.unop at hx
  change (pointwiseTorsionSubfunctor J F).sieveOfSection y ∈ J U.unop at hy
  apply J.superset_covering _ (J.intersection_covering hx hy)
  intro V i hi
  obtain ⟨⟨n, hn, hnx⟩, ⟨m, hm, hmy⟩⟩ := hi
  change n • (F.obj.map i.op).hom' x = 0 at hnx
  change m • (F.obj.map i.op).hom' y = 0 at hmy
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  show (n * m) • (F.obj.map i.op).hom' (x + y) = 0
  rw [(F.obj.map i.op).hom'.map_add]
  have hnx' : (n * m) • (F.obj.map i.op).hom' x = 0 := by
    rw [Nat.mul_comm n m, ← smul_smul, hnx, nsmul_zero]
  have hmy' : (n * m) • (F.obj.map i.op).hom' y = 0 := by
    rw [← smul_smul, hmy, nsmul_zero]
  rw [nsmul_add, hnx', hmy', zero_add]

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem locallyTorsion_neg (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ)
    (x : F.obj.obj U) (hx : x ∈ (locallyTorsionSubfunctor J F).obj U) :
    -x ∈ (locallyTorsionSubfunctor J F).obj U := by
  show (pointwiseTorsionSubfunctor J F).sieveOfSection (-x) ∈ J U.unop
  change (pointwiseTorsionSubfunctor J F).sieveOfSection x ∈ J U.unop at hx
  apply J.superset_covering _ hx
  intro V i hi
  obtain ⟨n, hn, hnx⟩ := hi
  change n • (F.obj.map i.op).hom' x = 0 at hnx
  refine ⟨n, hn, ?_⟩
  show n • (F.obj.map i.op).hom' (-x) = 0
  rw [(F.obj.map i.op).hom'.map_neg, neg_nsmul, hnx, neg_zero]

private def locallyTorsionSubgroup (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    AddSubgroup (F.obj.obj U) where
  carrier := (locallyTorsionSubfunctor J F).obj U
  zero_mem' := locallyTorsion_zero J F U
  add_mem' := fun {x y} hx hy => locallyTorsion_add J F U x y hx hy
  neg_mem' := fun {x} hx => locallyTorsion_neg J F U x hx

private def torsionSubfunctorPresheaf (F : Sheaf J AddCommGrpCat.{w}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (locallyTorsionSubgroup J F U)
  map {U V} i := AddCommGrpCat.ofHom {
    toFun := fun x => ⟨F.obj.map i x.val, (locallyTorsionSubfunctor J F).map i x.property⟩
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp
  }
  map_id U := by
    ext x
    simp
  map_comp i j := by
    ext x
    simp

private def torsionSubfunctorPresheafι (F : Sheaf J AddCommGrpCat.{w}) :
    torsionSubfunctorPresheaf J F ⟶ F.obj where
  app U := AddCommGrpCat.ofHom (locallyTorsionSubgroup J F U).subtype
  naturality U V i := by ext; rfl

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem torsionSubfunctorPresheaf_isSheaf (F : Sheaf J AddCommGrpCat.{w}) :
    Presheaf.IsSheaf J (torsionSubfunctorPresheaf J F) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J (s := forget AddCommGrpCat.{w})
  rw [isSheaf_iff_isSheaf_of_type]
  show Presieve.IsSheaf J (locallyTorsionSubfunctor J F).toFunctor
  apply Subfunctor.sheafify_isSheaf
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.2

private def torsionSubsheaf (F : Sheaf J AddCommGrpCat.{w}) :
    Sheaf J AddCommGrpCat.{w} :=
  ⟨torsionSubfunctorPresheaf J F, torsionSubfunctorPresheaf_isSheaf J F⟩

private def torsionSubsheafι (F : Sheaf J AddCommGrpCat.{w}) :
    torsionSubsheaf J F ⟶ F :=
  ⟨torsionSubfunctorPresheafι J F⟩

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem torsionSubsheafι_mono (F : Sheaf J AddCommGrpCat.{w}) :
    Mono (torsionSubsheafι J F) := by
  apply (sheafToPresheaf J AddCommGrpCat.{w}).mono_of_mono_map
  show Mono (torsionSubfunctorPresheafι J F)
  have (U : Cᵒᵖ) : Mono ((torsionSubfunctorPresheafι J F).app U) :=
    (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

private def torsionSubsheafLift {G F : Sheaf J AddCommGrpCat.{w}}
    (hG : torsionSheafProperty J G) (f : G ⟶ F) : G ⟶ torsionSubsheaf J F where
  hom := {
    app U := AddCommGrpCat.ofHom {
      toFun := fun x => ⟨f.hom.app U x, by
        change (pointwiseTorsionSubfunctor J F).sieveOfSection (f.hom.app U x) ∈ J U.unop
        obtain ⟨R, hR, hkill⟩ := hG U.unop x
        apply J.superset_covering _ hR
        intro V i hi
        obtain ⟨n, hn, hnx⟩ := hkill V i hi
        refine ⟨n, hn, ?_⟩
        have hnx' := congrArg (f.hom.app (op V)) hnx
        rw [_root_.map_nsmul, map_zero] at hnx'
        change n • (F.obj.map i.op) (f.hom.app U x) = 0
        rwa [← NatTrans.naturality_apply f.hom i.op x]⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp
    }
    naturality U V i := by
      ext x
      exact Subtype.ext (f.hom.naturality_apply i x)
  }

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem torsionSubsheafLift_fac {G F : Sheaf J AddCommGrpCat.{w}}
    (hG : torsionSheafProperty J G) (f : G ⟶ F) :
    torsionSubsheafLift J hG f ≫ torsionSubsheafι J F = f := by
  ext U x
  rfl

private theorem torsionSubsheafLift_unique {G F : Sheaf J AddCommGrpCat.{w}}
    (hG : torsionSheafProperty J G) (f : G ⟶ F) (g : G ⟶ torsionSubsheaf J F)
    (hg : g ≫ torsionSubsheafι J F = f) : g = torsionSubsheafLift J hG f := by
  have := torsionSubsheafι_mono J F
  apply (cancel_mono (torsionSubsheafι J F)).1
  rw [hg, torsionSubsheafLift_fac]

omit [HasSheafify J AddCommGrpCat.{w}] in
private theorem torsionSubsheaf_isTorsion (F : Sheaf J AddCommGrpCat.{w}) :
    torsionSheafProperty J (torsionSubsheaf J F) := fun _ x =>
  ⟨(pointwiseTorsionSubfunctor J F).sieveOfSection x.val, x.property,
    fun _ _ ⟨n, hn, hkill⟩ => ⟨n, hn, Subtype.ext hkill⟩⟩

private noncomputable def torsionSubsheafFunctor :
    Sheaf J AddCommGrpCat.{w} ⥤ TorsionSheaf J where
  obj F := ⟨torsionSubsheaf J F, torsionSubsheaf_isTorsion J F⟩
  map f := ObjectProperty.homMk (torsionSubsheafLift J
    (torsionSubsheaf_isTorsion J _) (torsionSubsheafι J _ ≫ f))
  map_id F := by
    apply InducedCategory.hom_ext
    change torsionSubsheafLift J (torsionSubsheaf_isTorsion J F)
      (torsionSubsheafι J F) = 𝟙 _
    exact (torsionSubsheafLift_unique J (torsionSubsheaf_isTorsion J F)
      (torsionSubsheafι J F) (𝟙 _) (by simp)).symm
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    have hX := torsionSubsheaf_isTorsion J X
    have hY := torsionSubsheaf_isTorsion J Y
    apply (torsionSubsheafLift_unique J hX
      (torsionSubsheafι J X ≫ f ≫ g)
      (torsionSubsheafLift J hX (torsionSubsheafι J X ≫ f) ≫
        torsionSubsheafLift J hY (torsionSubsheafι J Y ≫ g)) ?_).symm
    rw [Category.assoc, torsionSubsheafLift_fac J hY, ← Category.assoc,
      torsionSubsheafLift_fac J hX, Category.assoc]

private noncomputable def torsionSubsheafAdjunction :
    (torsionSheafProperty J).ι ⊣ torsionSubsheafFunctor J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X F =>
        { toFun := fun f => ObjectProperty.homMk (torsionSubsheafLift J X.2 f)
          invFun := fun g => g.hom ≫ torsionSubsheafι J F
          left_inv := torsionSubsheafLift_fac J X.2
          right_inv := fun g => InducedCategory.hom_ext
            (torsionSubsheafLift_unique J X.2 (g.hom ≫ torsionSubsheafι J F) g.hom rfl).symm }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

private theorem torsionSubsheafFunctor_additive :
    (torsionSubsheafFunctor J).Additive :=
  (torsionSubsheafAdjunction J).right_adjoint_additive

attribute [local instance] torsionSubsheafFunctor_additive

private noncomputable def torsionSubcomplex (K : CochainComplex
    (Sheaf J AddCommGrpCat.{w}) ℤ) : CochainComplex (TorsionSheaf J) ℤ :=
  (torsionSubsheafFunctor J).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj K

private noncomputable def torsionSubcomplexInclusion
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    (((torsionSheafProperty J).ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (torsionSubcomplex J K)) ⟶ K :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).hom.app K ≫
    (NatTrans.mapHomologicalComplex (torsionSubsheafAdjunction J).counit
      (ComplexShape.up ℤ)).app K

private theorem torsionSubsheafAdjunction_counit_app (F : Sheaf J AddCommGrpCat.{w}) :
    (torsionSubsheafAdjunction J).counit.app F = torsionSubsheafι J F :=
  rfl

private def intSectionHom (G : AddCommGrpCat.{w}) (x : G) :
    AddCommGrpCat.of (ULift.{w} ℤ) ⟶ G :=
  AddCommGrpCat.ofHom {
    toFun := fun n => (n.down : ℤ) • x
    map_zero' := by simp
    map_add' m n := by
      change (m.down + n.down) • x = _
      simp [add_zsmul]
  }

private theorem intSectionHom_apply_one (G : AddCommGrpCat.{w}) (x : G) :
    (intSectionHom G x).hom (ULift.up 1) = x := by simp [intSectionHom]

attribute [local simp] intSectionHom_apply_one

private theorem exists_local_kernel_lift {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (U V : C) (f : V ⟶ U) (x : S.X₂.obj.obj (op U))
    (n : ℕ) (hn : n • S.X₃.obj.map f.op (S.g.hom.app (op U) x) = 0) :
    ∃ y : S.X₁.obj.obj (op V),
      S.f.hom.app (op V) y = n • S.X₂.obj.map f.op x := by
  let E := (sheafSections J AddCommGrpCat.{w}).obj (op V)
  have : PreservesFiniteLimits E :=
    preservesFiniteLimits_of_natIso
      (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{w} (X := V)).symm
  have : HasBinaryProducts (Sheaf J AddCommGrpCat.{w}) := inferInstance
  have : E.Additive := E.additive_of_preserves_binary_products
  let hlim : IsLimit (E.mapCone (KernelFork.ofι S.f S.zero)) :=
    isLimitOfPreserves E hS.fIsKernel
  let a : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ E.obj S.X₂ :=
    intSectionHom (E.obj S.X₂) (n • S.X₂.obj.map f.op x)
  have ha : a ≫ E.map S.g = 0 := by
    ext z
    show (S.g.hom.app (op V))
      ((ULift.down z : ℤ) • (n • S.X₂.obj.map f.op x)) = 0
    rw [_root_.map_zsmul, _root_.map_nsmul, NatTrans.naturality_apply S.g.hom f.op x, hn]
    simp
  let c : KernelFork (E.map S.g) := KernelFork.ofι a ha
  let hlim' : IsLimit (KernelFork.ofι (E.map S.f)
      (by simp only [← E.map_comp, S.zero, Functor.map_zero]) : Fork (E.map S.g) 0) :=
    (isLimitMapConeForkEquiv' E S.zero) hlim
  let b : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ E.obj S.X₁ := hlim'.lift c
  have hfac : b ≫ E.map S.f = a := by
    simpa [b, c] using hlim'.fac c WalkingParallelPair.zero
  refine ⟨b.hom (ULift.up 1), ?_⟩
  simpa [E, sheafSections, a, intSectionHom] using
    congrArg (fun k => k.hom (ULift.up 1)) hfac

/-- Torsion abelian sheaves form a Serre subcategory. -/
@[stacks 0DD7 "Serre subcategory"]
public instance torsionSheafProperty_isSerreClass :
    (torsionSheafProperty J).IsSerreClass where
  exists_zero := by
    refine ⟨0, isZero_zero _, fun U x => ⟨⊤, J.top_mem U, fun V f hf => ⟨1, by omega, ?_⟩⟩⟩
    have hx : x = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp
      (((sheafSections J AddCommGrpCat.{w}).obj (op U)).map_isZero
        (isZero_zero (Sheaf J AddCommGrpCat.{w})))).elim _ _
    simp [hx]
  prop_of_mono := by
    intro F G f hf hG U x
    obtain ⟨R, hR, hkill⟩ := hG U (f.hom.app (op U) x)
    refine ⟨R, hR, ?_⟩
    intro V g hg
    obtain ⟨n, hn, hk⟩ := hkill V g hg
    have hinj : Function.Injective (f.hom.app (op V)) := by
      have : Mono ((sheafToPresheaf J AddCommGrpCat.{w}).map f) := inferInstance
      have : Mono (((sheafToPresheaf J AddCommGrpCat.{w}).map f).app (op V)) := inferInstance
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    refine ⟨n, hn, hinj ?_⟩
    rwa [_root_.map_nsmul, map_zero, NatTrans.naturality_apply f.hom g.op x]
  prop_of_epi := by
    intro F G f hf hF U y
    let R := Presheaf.imageSieve f.hom y
    have hR : R ∈ J U := (Stacks.Sites.LocalImage.epi_localSurjective J f).imageSieve_mem y
    let T : ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄, R g → Sieve V := fun {V} {g} hg => by
      change ∃ z, f.hom.app (op V) z = G.obj.map g.op y at hg
      exact (hF V hg.choose).choose
    have hT : ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄ (hg : R g), T hg ∈ J V := by
      intro V g hg
      change ∃ z, f.hom.app (op V) z = G.obj.map g.op y at hg
      exact (hF V hg.choose).choose_spec.1
    refine ⟨Sieve.bind R T, J.bind_covering hR hT, ?_⟩
    intro W h hh
    obtain ⟨V, k, g, hg, hk, rfl⟩ := hh
    change ∃ z, f.hom.app (op V) z = G.obj.map g.op y at hg
    let z := hg.choose
    have hz := hg.choose_spec
    dsimp only [T] at hk
    obtain ⟨n, hn, hkill⟩ := (hF V z).choose_spec.2 W k hk
    refine ⟨n, hn, ?_⟩
    have hmap : f.hom.app (op W) (F.obj.map k.op z) =
        G.obj.map (k ≫ g).op y := by
      rw [NatTrans.naturality_apply f.hom k.op z, hz]
      simp [Functor.map_comp]
    have hkill' := congrArg (f.hom.app (op W)) hkill
    rwa [_root_.map_nsmul, map_zero, hmap] at hkill'
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃ U x
    obtain ⟨R, hR, hq⟩ := h₃ U (S.g.hom.app (op U) x)
    let ksec : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄, R u → S.X₁.obj.obj (op V) :=
      fun {V} {u} hu =>
        (exists_local_kernel_lift J hS U V u x (hq V u hu).choose
          (hq V u hu).choose_spec.2).choose
    have hksec : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄ (hu : R u),
        S.f.hom.app (op V) (ksec hu) =
          (hq V u hu).choose • S.X₂.obj.map u.op x :=
      fun V u hu => (exists_local_kernel_lift J hS U V u x (hq V u hu).choose
        (hq V u hu).choose_spec.2).choose_spec
    let T : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄, R u → Sieve V := fun {_V} {_u} hu =>
      (h₁ _ (ksec hu)).choose
    have hT : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄ (hu : R u), T hu ∈ J V :=
      fun V u hu => (h₁ V (ksec hu)).choose_spec.1
    refine ⟨Sieve.bind R T, J.bind_covering hR hT, ?_⟩
    intro W h hh
    obtain ⟨V, k, u, hu, hk, rfl⟩ := hh
    dsimp only [T] at hk
    obtain ⟨m, hm, hkill⟩ := (h₁ V (ksec hu)).choose_spec.2 W k hk
    have hkill' := congrArg (S.f.hom.app (op W)) hkill
    rw [_root_.map_nsmul, map_zero, NatTrans.naturality_apply S.f.hom k.op (ksec hu),
      hksec hu, _root_.map_nsmul, smul_smul, ← S.X₂.obj.map_comp_apply, ← op_comp] at hkill'
    exact ⟨m * (hq V u hu).choose, Nat.mul_pos hm (hq V u hu).choose_spec.1,
      by simpa using hkill'⟩

/-- The inclusion of torsion sheaves into abelian sheaves preserves finite limits. -/
public instance torsionSheafProperty_preservesFiniteLimits :
    PreservesFiniteLimits.{max u w, max u w,
      max (max (max (w + 1) u) w) v, max (max (max (w + 1) u) w) v}
      (torsionSheafProperty J).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass
    (C := Sheaf J AddCommGrpCat.{w}) _

/-- The inclusion of torsion sheaves into abelian sheaves preserves finite colimits. -/
public instance torsionSheafProperty_preservesFiniteColimits :
    PreservesFiniteColimits.{max u w, max u w,
      max (max (max (w + 1) u) w) v, max (max (max (w + 1) u) w) v}
      (torsionSheafProperty J).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass
    (C := Sheaf J AddCommGrpCat.{w}) _

omit [HasSheafify J AddCommGrpCat.{w}] in
private lemma section_kernel_lift {F G K : Sheaf J AddCommGrpCat.{w}}
    (f : F ⟶ G) (g : G ⟶ K) (hfg : f ≫ g = 0)
    (hf : IsLimit (KernelFork.ofι f hfg)) (U : C)
    (x : G.obj.obj (op U)) (hx : g.hom.app (op U) x = 0) :
    ∃ y : F.obj.obj (op U), f.hom.app (op U) y = x := by
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  let S := ShortComplex.mk f g hfg
  exact (S.map E).ab_exact_iff.mp
    ((S.map E).exact_of_f_is_kernel (KernelFork.mapIsLimit _ hf E)) x hx

omit [HasSheafify J AddCommGrpCat.{w}] in
private lemma section_eq_zero_of_locally_zero (F : Sheaf J AddCommGrpCat.{w})
    (U : C) (x : F.obj.obj (op U)) (R : Sieve U) (hR : R ∈ J U)
    (hx : ∀ (V : C) (f : V ⟶ U), R f → F.obj.map f.op x = 0) : x = 0 := by
  have hF := (isSheaf_iff_isSheaf_of_type J _).mp
    (GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.2
      (F := forget AddCommGrpCat.{w}))
  apply (hF.isSeparated _ hR).ext
  intro V f hf
  show F.obj.map f.op x = F.obj.map f.op 0
  exact (hx V f hf).trans (map_zero _).symm

omit [HasSheafify J AddCommGrpCat.{w}] in
private lemma locallyTorsion_of_nsmul (F : Sheaf J AddCommGrpCat.{w})
    (U : Cᵒᵖ) (x : F.obj.obj U) (n : ℕ) (hn : 0 < n)
    (hx : n • x ∈ (locallyTorsionSubfunctor J F).obj U) :
    x ∈ (locallyTorsionSubfunctor J F).obj U := by
  show (pointwiseTorsionSubfunctor J F).sieveOfSection x ∈ J U.unop
  apply J.superset_covering _ hx
  intro V f hf
  obtain ⟨m, hm, hmx⟩ := hf
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  change m • (F.obj.map f.op) (n • x) = 0 at hmx
  show (m * n) • F.obj.map f.op x = 0
  simpa only [_root_.map_nsmul, smul_smul] using hmx

private lemma section_cokernel_torsion_eq_zero_iff
    (F : Sheaf J AddCommGrpCat.{w}) (U : C) (x : F.obj.obj (op U)) :
    (cokernel.π (torsionSubsheafι J F)).hom.app (op U) x = 0 ↔
      x ∈ (locallyTorsionSubfunctor J F).obj (op U) := by
  have : Mono (torsionSubsheafι J F) := torsionSubsheafι_mono J F
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := section_kernel_lift J (torsionSubsheafι J F)
      (cokernel.π (torsionSubsheafι J F)) (cokernel.condition _)
      (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)) U x hx
    change y.val = x at hy
    exact hy ▸ y.property
  · exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun a => a.hom)
        (cokernel.condition (torsionSubsheafι J F))) (op U))
      (⟨x, hx⟩ : (torsionSubsheaf J F).obj.obj (op U))

private lemma section_cokernel_torsion_nsmul_injective
    (F : Sheaf J AddCommGrpCat.{w}) (U : C) (n : ℕ) (hn : 0 < n) :
    Function.Injective (fun x : (cokernel (torsionSubsheafι J F)).obj.obj (op U) =>
      n • x) := by
  suffices h : ∀ x : (cokernel (torsionSubsheafι J F)).obj.obj (op U),
      n • x = 0 → x = 0 by
    intro x y hxy
    change n • x = n • y at hxy
    exact sub_eq_zero.mp (h (x - y) (by rw [nsmul_sub, hxy, sub_self]))
  intro x hx
  let q := cokernel.π (torsionSubsheafι J F)
  apply section_eq_zero_of_locally_zero J _ U x (Presheaf.imageSieve q.hom x)
    ((Stacks.Sites.LocalImage.epi_localSurjective J q).imageSieve_mem x)
  intro V f hf
  obtain ⟨y, hy⟩ := hf
  rw [← hy]
  apply (section_cokernel_torsion_eq_zero_iff J F V y).mpr
  apply locallyTorsion_of_nsmul J F (op V) y n hn
  apply (section_cokernel_torsion_eq_zero_iff J F V (n • y)).mp
  show q.hom.app (op V) (n • y) = 0
  rw [_root_.map_nsmul, hy, ← _root_.map_nsmul, hx, map_zero]

omit [HasSheafify J AddCommGrpCat.{w}] in
private lemma isZero_of_torsion_of_nsmul_injective
    (F : Sheaf J AddCommGrpCat.{w}) (hF : torsionSheafProperty J F)
    (hmono : ∀ (U : C) (n : ℕ), 0 < n →
      Function.Injective (fun x : F.obj.obj (op U) => n • x)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  show x = 0
  obtain ⟨R, hR, hx⟩ := hF U.unop x
  apply section_eq_zero_of_locally_zero J F U.unop x R hR
  intro V f hf
  obtain ⟨n, hn, hnx⟩ := hx V f hf
  apply hmono V n hn
  simpa only [nsmul_zero] using hnx

omit [HasSheafify J AddCommGrpCat.{w}] in
/-- `n • 𝟙 F` is a monomorphism iff multiplication by `n` is injective on all sections. -/
private lemma mono_nsmul_id_iff (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Mono (n • 𝟙 F) ↔ ∀ U : Cᵒᵖ, Function.Injective (fun x : F.obj.obj U => n • x) := by
  rw [← (sheafToPresheaf J AddCommGrpCat.{w}).mono_map_iff_mono, NatTrans.mono_iff_mono_app]
  refine forall_congr' fun U => ?_
  rw [AddCommGrpCat.mono_iff_injective]
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  change Function.Injective (E.map (n • 𝟙 F)) ↔ _
  rw [E.map_nsmul, E.map_id]
  exact Iff.rfl

private lemma mono_nsmul_cokernel_torsionSubsheafι
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (hn : 0 < n) :
    Mono (n • 𝟙 (cokernel (torsionSubsheafι J F))) :=
  (mono_nsmul_id_iff J _ n).mpr fun U => section_cokernel_torsion_nsmul_injective J F U.unop n hn

private lemma isIso_nsmul_cokernel_torsionSubsheafι
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (hn : 0 < n)
    [Epi (n • 𝟙 F)] : IsIso (n • 𝟙 (cokernel (torsionSubsheafι J F))) := by
  have := mono_nsmul_cokernel_torsionSubsheafι J F n hn
  have heq : (n • 𝟙 F) ≫ cokernel.π (torsionSubsheafι J F) =
      cokernel.π (torsionSubsheafι J F) ≫
        (n • 𝟙 (cokernel (torsionSubsheafι J F))) := by
    simp
  have : Epi (n • 𝟙 (cokernel (torsionSubsheafι J F))) := epi_of_epi_fac heq.symm
  exact isIso_of_mono_of_epi _

private lemma torsion_homology_of_torsion_terms
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (hK : ∀ i, torsionSheafProperty J (K.X i)) (i : ℤ) :
    torsionSheafProperty J (K.homology i) :=
  (torsionSheafProperty J).prop_of_epi (K.homologyπ i)
    ((torsionSheafProperty J).prop_of_mono (K.iCycles i) (hK i))

private lemma torsionSubcomplexInclusion_quasiIso_of_divisible
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (hdiv : ∀ (i : ℤ) (n : ℕ), 0 < n → Epi (n • 𝟙 (K.X i)))
    (hK : ∀ i, torsionSheafProperty J (K.homology i)) :
    QuasiIso (torsionSubcomplexInclusion J K) := by
  let f := torsionSubcomplexInclusion J K
  have hf : Mono f := HomologicalComplex.mono_of_mono_f f (fun i => by
    show Mono ((torsionSubsheafAdjunction J).counit.app (K.X i))
    rw [torsionSubsheafAdjunction_counit_app]
    exact torsionSubsheafι_mono J (K.X i))
  let Q := cokernel f
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f) }
  apply CategoryTheory.quasiIso_of_shortExact_of_isZero_homology hS
  intro i
  have hT (j : ℤ) : torsionSheafProperty J (S.X₁.homology j) :=
    torsion_homology_of_torsion_terms J _ (fun k => torsionSubsheaf_isTorsion J (K.X k)) j
  have hQ : torsionSheafProperty J (Q.homology i) :=
    (torsionSheafProperty J).prop_X₂_of_exact
      (hS.homology_exact₃ i (i + 1) rfl) (hK i) (hT (i + 1))
  apply isZero_of_torsion_of_nsmul_injective J _ hQ
  intro U n hn
  refine (mono_nsmul_id_iff J _ n).mp ?_ (op U)
  have (j : ℤ) : IsIso ((n • 𝟙 Q).f j) := by
    let E := HomologicalComplex.eval (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ) j
    show IsIso (E.map (n • 𝟙 Q))
    rw [E.map_nsmul, E.map_id]
    let e := PreservesCokernel.iso E f
    change Q.X j ≅ cokernel (torsionSubsheafι J (K.X j)) at e
    have := hdiv j n hn
    have := isIso_nsmul_cokernel_torsionSubsheafι J (K.X j) n hn
    have hi : IsIso (e.hom ≫ (n • 𝟙 _) ≫ e.inv) := inferInstance
    show IsIso (n • 𝟙 (Q.X j))
    simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id] using hi
  have : IsIso (n • 𝟙 Q) := HomologicalComplex.Hom.isIso_of_components _
  let H := HomologicalComplex.homologyFunctor (Sheaf J AddCommGrpCat.{w})
    (ComplexShape.up ℤ) i
  have hi : IsIso (H.map (n • 𝟙 Q)) := inferInstance
  have : IsIso (n • 𝟙 (Q.homology i)) := by
    rwa [H.map_nsmul, H.map_id] at hi
  infer_instance

private def reducedCharacterGroup (A : AddCommGrpCat.{w}) :
    AddSubgroup (CharacterModule A → AddCircle (1 : ℚ)) where
  carrier := {x | x 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x 0 + y 0 = 0
    rw [hx, hy, zero_add]
  neg_mem' := by
    intro x hx
    change -x 0 = 0
    rw [hx, neg_zero]

private def reducedCharacterFunctor : AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} where
  obj A := AddCommGrpCat.of (reducedCharacterGroup A)
  map {A B} f := AddCommGrpCat.ofHom {
    toFun := fun x => ⟨fun χ => x.val (χ.comp f.hom), by
      change x.val ((0 : B →+ AddCircle (1 : ℚ)).comp f.hom) = 0
      exact (congrArg x.val (AddMonoidHom.zero_comp f.hom)).trans x.property⟩
    map_zero' := rfl
    map_add' := by intros; rfl }
  map_id A := by ext x χ; rfl
  map_comp f g := by ext x χ; rfl

private theorem reducedCharacterFunctor_preservesZeroMorphisms :
    reducedCharacterFunctor.{w}.PreservesZeroMorphisms where
  map_zero A B := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change reducedCharacterGroup A at x
    apply Subtype.ext
    funext χ
    change B →+ AddCircle (1 : ℚ) at χ
    show x.val (χ.comp (0 : A →+ B)) = 0
    exact (congrArg x.val (AddMonoidHom.comp_zero χ)).trans x.property

attribute [local instance] reducedCharacterFunctor_preservesZeroMorphisms

private def reducedCharacterInclusion :
    𝟭 AddCommGrpCat.{w} ⟶ reducedCharacterFunctor where
  app A := AddCommGrpCat.ofHom {
    toFun := fun a => ⟨fun χ => χ a, rfl⟩
    map_zero' := by ext χ; exact map_zero χ
    map_add' := by intro a b; ext χ; exact map_add χ a b }
  naturality A B f := by ext a; rfl

private lemma reducedCharacterInclusion_mono (A : AddCommGrpCat.{w}) :
    Mono (reducedCharacterInclusion.app A) := by
  rw [AddCommGrpCat.mono_iff_injective]
  exact (injective_iff_map_eq_zero _).mpr fun a ha =>
    CharacterModule.eq_zero_of_character_apply fun χ => congrArg (fun x => x.val χ) ha

private lemma reducedCharacterFunctor_epi_nsmul (A : AddCommGrpCat.{w})
    (n : ℕ) (hn : 0 < n) : Epi (n • 𝟙 (reducedCharacterFunctor.obj A)) := by
  classical
  let := AddGroup.divisibleByNatOfDivisibleByInt (AddCircle (1 : ℚ))
  rw [AddCommGrpCat.epi_iff_surjective]
  intro x
  change reducedCharacterGroup A at x
  let y : reducedCharacterGroup A :=
    ⟨fun χ => if χ = 0 then 0 else DivisibleBy.div (x.val χ) n, by
      show (if (0 : CharacterModule A) = 0 then 0 else _) = 0
      simp only [ite_true]⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  funext χ
  show n • (if χ = 0 then 0 else DivisibleBy.div (x.val χ) n) = x.val χ
  split_ifs with hχ
  · subst χ
    simpa only [nsmul_zero] using x.property.symm
  · exact DivisibleBy.div_cancel _ hn.ne'

private def divisiblePresheafFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (whiskeringRight Cᵒᵖ AddCommGrpCat.{w} AddCommGrpCat.{w}).obj reducedCharacterFunctor

private theorem divisiblePresheafFunctor_preservesZeroMorphisms :
    (divisiblePresheafFunctor (C := C)).PreservesZeroMorphisms where
  map_zero P Q := by
    apply NatTrans.ext
    funext U
    show reducedCharacterFunctor.map (0 : P.obj U ⟶ Q.obj U) = 0
    exact reducedCharacterFunctor.map_zero _ _

attribute [local instance] divisiblePresheafFunctor_preservesZeroMorphisms

private def divisiblePresheafInclusion :
    𝟭 (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⟶ divisiblePresheafFunctor where
  app P := whiskerLeft P reducedCharacterInclusion
  naturality P Q f := by ext U x; rfl

private lemma divisiblePresheafInclusion_mono (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Mono (divisiblePresheafInclusion.app P) := by
  have (U : Cᵒᵖ) : Mono ((divisiblePresheafInclusion.app P).app U) :=
    reducedCharacterInclusion_mono (P.obj U)
  exact NatTrans.mono_of_mono_app _

private def divisibleSheafFunctor : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙ divisiblePresheafFunctor ⋙
    presheafToSheaf J AddCommGrpCat.{w}

private theorem divisibleSheafFunctor_preservesZeroMorphisms :
    (divisibleSheafFunctor J).PreservesZeroMorphisms := by
  dsimp only [divisibleSheafFunctor]
  infer_instance

attribute [local instance] divisibleSheafFunctor_preservesZeroMorphisms

private def divisibleSheafInclusion : 𝟭 (Sheaf J AddCommGrpCat.{w}) ⟶
    divisibleSheafFunctor J :=
  (asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit).inv ≫
    whiskerRight (whiskerLeft (sheafToPresheaf J AddCommGrpCat.{w})
      divisiblePresheafInclusion) (presheafToSheaf J AddCommGrpCat.{w})

private lemma divisibleSheafInclusion_mono (F : Sheaf J AddCommGrpCat.{w}) :
    Mono ((divisibleSheafInclusion J).app F) := by
  have := divisiblePresheafInclusion_mono F.obj
  show Mono ((asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit).inv.app F ≫
    (presheafToSheaf J AddCommGrpCat.{w}).map (divisiblePresheafInclusion.app F.obj))
  infer_instance

private lemma divisibleSheafFunctor_epi_nsmul (F : Sheaf J AddCommGrpCat.{w})
    (n : ℕ) (hn : 0 < n) : Epi (n • 𝟙 ((divisibleSheafFunctor J).obj F)) := by
  let P := divisiblePresheafFunctor.obj F.obj
  have (U : Cᵒᵖ) : Epi ((n • 𝟙 P).app U) := by
    rw [NatTrans.app_nsmul, NatTrans.id_app]
    exact reducedCharacterFunctor_epi_nsmul (F.obj.obj U) n hn
  have : Epi (n • 𝟙 P) := NatTrans.epi_of_epi_app _
  let A := presheafToSheaf J AddCommGrpCat.{w}
  have hepi : Epi (A.map (n • 𝟙 P)) := inferInstance
  rwa [A.map_nsmul, A.map_id] at hepi

private def divisibleComplexTermFunctor :
    CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ :=
  (divisibleSheafFunctor J).mapHomologicalComplex (ComplexShape.up ℤ)

private def divisibleComplexTermInclusion
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    K ⟶ (divisibleComplexTermFunctor J).obj K :=
  (NatTrans.mapHomologicalComplex (divisibleSheafInclusion J) (ComplexShape.up ℤ)).app K

private lemma divisibleComplexTermInclusion_mono
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    Mono (divisibleComplexTermInclusion J K) :=
  HomologicalComplex.mono_of_mono_f _ (fun i => divisibleSheafInclusion_mono J (K.X i))

private lemma exists_torsionComplex_comparison
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (hK : ∀ i, torsionSheafProperty J (K.homology i)) :
    ∃ (I : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (f : K ⟶ I),
      QuasiIso f ∧ QuasiIso (torsionSubcomplexInclusion J I) := by
  have := divisibleComplexTermInclusion_mono J K
  obtain ⟨I, f, hf, hI⟩ := exists_divisible_complex_replacement
    (divisibleComplexTermInclusion J K)
    (fun i n hn => divisibleSheafFunctor_epi_nsmul J (K.X i) n hn)
  exact ⟨I, f, hf, torsionSubcomplexInclusion_quasiIso_of_divisible J I hI fun i =>
    (torsionSheafProperty J).prop_of_iso (asIso (HomologicalComplex.homologyMap f i)) (hK i)⟩

private def inclusionMapComplexHomologyIso (i : ℤ) :
    (torsionSheafProperty J).ι.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ) i ≅
    HomologicalComplex.homologyFunctor (TorsionSheaf J) (ComplexShape.up ℤ) i ⋙
      (torsionSheafProperty J).ι :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso (torsionSheafProperty J).ι)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (TorsionSheaf J) (ComplexShape.up ℤ) i).map f)
      (torsionSheafProperty J).ι)

private lemma inclusionMapHomotopy_quasiIso_iff
    {X Y : HomotopyCategory (TorsionSheaf J) (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (TorsionSheaf J) (ComplexShape.up ℤ) f ↔
      HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)
        (((torsionSheafProperty J).ι.mapHomotopyCategory (ComplexShape.up ℤ)).map f) := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  show HomotopyCategory.quasiIso (TorsionSheaf J) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (TorsionSheaf J) (ComplexShape.up ℤ)).map f) ↔
    HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)).map
        (((torsionSheafProperty J).ι.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (torsionSheafProperty J).ι).symm

variable [HasDerivedCategory (Sheaf J AddCommGrpCat.{w})]

/-- The property that all cohomology sheaves of a derived object are torsion. -/
public def torsionCohomologyProperty :
    ObjectProperty (DerivedCategory (Sheaf J AddCommGrpCat.{w})) :=
  fun K ↦ ∀ i : ℤ,
    torsionSheafProperty J
      ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{w}) i).obj K)

/-- The full subcategory of the derived category consisting of objects with torsion
cohomology sheaves. -/
@[sga "4 XVII 5.1.13"]
public abbrev TorsionDerivedCategory :=
  (torsionCohomologyProperty J).FullSubcategory

variable [HasDerivedCategory (TorsionSheaf J)]

private def inclusionMapDerivedHomologyIso (i : ℤ) :
    (torsionSheafProperty J).ι.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{w}) i ≅
    DerivedCategory.homologyFunctor (TorsionSheaf J) i ⋙ (torsionSheafProperty J).ι :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (TorsionSheaf J) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ ((torsionSheafProperty J).ι.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{w}) i))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor (TorsionSheaf J) i ⋙
      (torsionSheafProperty J).ι)) _ _
    (Functor.isoWhiskerRight (torsionSheafProperty J).ι.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{w}) i) ≪≫
      Functor.isoWhiskerLeft ((torsionSheafProperty J).ι.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors (Sheaf J AddCommGrpCat.{w}) i) ≪≫
      inclusionMapComplexHomologyIso J i ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors (TorsionSheaf J) i).symm
        (torsionSheafProperty J).ι)

private lemma inclusionMapDerived_has_torsionCohomology
    (K : DerivedCategory (TorsionSheaf J)) :
    torsionCohomologyProperty J ((torsionSheafProperty J).ι.mapDerivedCategory.obj K) :=
  fun i => (torsionSheafProperty J).prop_of_iso ((inclusionMapDerivedHomologyIso J i).app K).symm
      ((DerivedCategory.homologyFunctor (TorsionSheaf J) i).obj K).property

private def torsionDerivedFunctor :
    DerivedCategory (TorsionSheaf J) ⥤ TorsionDerivedCategory J :=
  (torsionCohomologyProperty J).lift (torsionSheafProperty J).ι.mapDerivedCategory
    (inclusionMapDerived_has_torsionCohomology J)

private def torsionDerivedFunctorCompInclusionIso :
    torsionDerivedFunctor J ⋙ (torsionCohomologyProperty J).ι ≅
      (torsionSheafProperty J).ι.mapDerivedCategory :=
  (torsionCohomologyProperty J).liftCompιIso _ _

private lemma inclusionMapDerived_full_faithful :
    (torsionSheafProperty J).ι.mapDerivedCategory.Full ∧
      (torsionSheafProperty J).ι.mapDerivedCategory.Faithful := by
  let F := (torsionSheafProperty J).ι
  let c := ComplexShape.up ℤ
  let adj := (torsionSubsheafAdjunction J).mapHomotopyCategory c
  have : (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) c).HasTwoOutOfThreeProperty :=
    homotopyCategory_quasiIso_hasTwoOutOfThreeProperty
  apply localized_full_faithful_of_replacements
    (HomotopyCategory.quasiIso (TorsionSheaf J) c)
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) c)
    DerivedCategory.Qh DerivedCategory.Qh (F.mapHomotopyCategory c)
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh.symm
    (inclusionMapHomotopy_quasiIso_iff J)
  rintro ⟨Y⟩ ⟨Z⟩ s hs
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  have hs' : QuasiIso s :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
  have hZ (i : ℤ) : torsionSheafProperty J (Z.homology i) :=
    (torsionSheafProperty J).prop_of_iso (asIso (HomologicalComplex.homologyMap s i))
      (torsion_homology_of_torsion_terms J _ (fun j => (Y.X j).property) i)
  obtain ⟨I, f, hf, hc⟩ := exists_torsionComplex_comparison J Z hZ
  let Ih := (HomotopyCategory.quotient _ c).obj I
  refine ⟨Ih, (HomotopyCategory.quotient _ c).map f,
    ((torsionSubsheafFunctor J).mapHomotopyCategory c).obj Ih,
    adj.counit.app Ih, (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf, ?_,
    fun X => (adj.homEquiv X Ih).symm.bijective⟩
  have heq : adj.counit.app Ih =
      (HomotopyCategory.quotient _ c).map (torsionSubcomplexInclusion J I) := by
    show (HomotopyCategory.quotient _ c).map _ =
      (HomotopyCategory.quotient _ c).map _
    congr 1
  rw [heq]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hc

private lemma torsionDerivedFunctor_essSurj : (torsionDerivedFunctor J).EssSurj := by
  refine ⟨fun M => ?_⟩
  let K := DerivedCategory.Q.objPreimage M.obj
  let e : DerivedCategory.Q.obj K ≅ M.obj := DerivedCategory.Q.objObjPreimageIso M.obj
  have hK (i : ℤ) : torsionSheafProperty J (K.homology i) :=
    (torsionSheafProperty J).prop_of_iso
      (((DerivedCategory.homologyFunctor _ i).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app K) (M.property i)
  obtain ⟨I, f, hf, hc⟩ := exists_torsionComplex_comparison J K hK
  refine ⟨DerivedCategory.Q.obj (torsionSubcomplex J I), ⟨?_⟩⟩
  apply ObjectProperty.isoMk
  exact ((torsionSheafProperty J).ι.mapDerivedCategoryFactors.app (torsionSubcomplex J I)) ≪≫
    asIso (DerivedCategory.Q.map (torsionSubcomplexInclusion J I)) ≪≫
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ e

/-- **Stacks 0DD7.** The derived category of torsion abelian sheaves is equivalent to the full
subcategory of the derived category of all abelian sheaves consisting of objects with torsion
cohomology.  Under this equivalence, the inclusion is the derived functor of the inclusion of
torsion sheaves. -/
@[stacks 0DD7 "derived equivalence"]
public theorem exists_torsionDerivedEquivalence :
    ∃ e : DerivedCategory (TorsionSheaf J) ≌ TorsionDerivedCategory J,
      Nonempty (e.functor ⋙ (torsionCohomologyProperty J).ι ≅
        (torsionSheafProperty J).ι.mapDerivedCategory) := by
  obtain ⟨_, _⟩ := inclusionMapDerived_full_faithful J
  have : (torsionDerivedFunctor J).Full :=
    Functor.Full.of_comp_faithful_iso (torsionDerivedFunctorCompInclusionIso J)
  have : (torsionDerivedFunctor J).Faithful :=
    Functor.Faithful.of_comp_iso (torsionDerivedFunctorCompInclusionIso J)
  have := torsionDerivedFunctor_essSurj J
  have : (torsionDerivedFunctor J).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨(torsionDerivedFunctor J).asEquivalence, ⟨torsionDerivedFunctorCompInclusionIso J⟩⟩

end Stacks.Torsion
