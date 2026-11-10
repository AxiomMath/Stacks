module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Category
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.RingTheory.Module.ReduceModIdealExact

/-!
# Ext over adic quotients: inverse limits of adic comparisons (Tag 0EH0, part 1)

Finite projective resolutions of finite modules over a Noetherian ring, inverse limits under
shifted inverse maps, the adic-comparison predicate `HasAdicComparison`, quotient equivalences
for base change and `ULift`, and the adic comparison for the homology of a complex of finite
modules.
-/

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped TensorProduct ModuleCat.Algebra

namespace Stacks.AdicSystem.ExtFlatBaseChange

section FiniteResolution

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [Small.{v} R]

private lemma enoughProjectivesFG : EnoughProjectives (FGModuleCat.{v} R) := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  refine ⟨fun M => ?_⟩
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
  have hP : Projective (FGModuleCat.of R P) :=
    F.projective_of_map_projective
      (inferInstanceAs (Projective (ModuleCat.of R P)))
  have hfe : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  have hfe' : Epi (FGModuleCat.ofHom f) := F.epi_of_epi_map hfe
  exact ⟨{ p := FGModuleCat.of R P, f := FGModuleCat.ofHom f }⟩

omit [IsNoetherianRing R] in
private lemma preservesProjectiveObjectsFG :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesProjectiveObjects := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  refine ⟨fun {M} hM => ?_⟩
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
  have hfe : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  let f' : FGModuleCat.of R P ⟶ M := FGModuleCat.ofHom f
  have hfe' : Epi f' := F.epi_of_epi_map hfe
  let g := Projective.factorThru (𝟙 M) f'
  have hg : f.comp g.hom.hom = LinearMap.id :=
    congrArg (fun h => h.hom.hom) (Projective.factorThru_comp (𝟙 M) f')
  have : Module.Projective R M := Module.Projective.of_split g.hom.hom f hg
  exact inferInstanceAs (Projective (ModuleCat.of R M))

lemma exists_finite_projectiveResolution (M : ModuleCat.{v} R)
    [Module.Finite R M] :
    ∃ P : ProjectiveResolution M, ∀ n, Module.Finite R (P.complex.X n) := by
  let := enoughProjectivesFG.{u, v} R
  let := preservesProjectiveObjectsFG.{u, v} R
  let P := ProjectiveResolution.of (FGModuleCat.of R M)
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  have : F.Additive := ⟨rfl⟩
  exact ⟨F.mapProjectiveResolution P, fun n => inferInstanceAs
    (Module.Finite R (P.complex.X n))⟩

end FiniteResolution

section Limits

-- `tr` and `ProIso` are supplied by the untagged `InverseSequence` replay in
-- `AdicSystem/Homology.lean`, which replaced the former legacy `Ch20.Sec39.Tag0H3D` import.
open InverseSequence

private lemma exists_limitIso_of_shift_inverse
    {C : Type*} [Category* C] (F G : ℕᵒᵖ ⥤ C) [HasLimit F] [HasLimit G]
    (φ : F ⟶ G) (c : ℕ)
    (b : ∀ n, G.obj (op (n + c)) ⟶ F.obj (op n))
    (hbφ : ∀ n, b n ≫ φ.app (op n) = tr G (Nat.le_add_right n c))
    (hφb : ∀ n, φ.app (op (n + c)) ≫ b n = tr F (Nat.le_add_right n c)) :
    ∃ e : limit F ≅ limit G,
      ∀ n, e.hom ≫ limit.π G (op n) = limit.π F (op n) ≫ φ.app (op n) := by
  let g (n : ℕ) := limit.π G (op (n + c)) ≫ b n
  have hg (n k : ℕ) (h : n + c ≤ k) :
      g n = (limit.π G (op (k + c)) ≫ b k) ≫ tr F (by omega : n ≤ k) := by
    calc
      g n = limit.π G (op (k + c)) ≫ tr G (by omega : n + c ≤ k + c) ≫ b n := by
        rw [← Category.assoc, tr, limit.w]
      _ = limit.π G (op (k + c)) ≫ (b k ≫ φ.app (op k)) ≫ tr G h ≫ b n := by
        rw [hbφ, ← Category.assoc (tr G _) (tr G h), ProIso.tr_trans]
      _ = limit.π G (op (k + c)) ≫ b k ≫ tr F h ≫ φ.app (op (n + c)) ≫ b n := by
        have hn : tr F h ≫ φ.app (op (n + c)) = φ.app (op k) ≫ tr G h :=
          φ.naturality (homOfLE h).op
        simp only [Category.assoc]
        rw [← reassoc_of% hn]
      _ = (limit.π G (op (k + c)) ≫ b k) ≫ tr F (by omega : n ≤ k) := by
        rw [hφb, ProIso.tr_trans]
        simp only [Category.assoc]
  let cone : Cone F := ⟨limit G, {
    app := fun j => g j.unop
    naturality := by
      intro j k f
      have h : k.unop ≤ j.unop := leOfHom f.unop
      have hf : f = (homOfLE h).op := Subsingleton.elim _ _
      subst f
      change 𝟙 (limit G) ≫ g k.unop = g j.unop ≫ tr F h
      rw [Category.id_comp, hg k.unop (j.unop + c) (Nat.add_le_add_right h c),
        hg j.unop (j.unop + c) le_rfl]
      simp only [Category.assoc, ProIso.tr_trans] }⟩
  let inv : limit G ⟶ limit F := limit.lift F cone
  have hi (n : ℕ) : inv ≫ limit.π F (op n) = g n := limit.lift_π cone (op n)
  refine ⟨⟨limMap φ, inv, ?_, ?_⟩, fun n => limMap_π φ (op n)⟩
  · apply limit.hom_ext
    intro j
    rw [Category.assoc, hi j.unop]
    change limMap φ ≫ limit.π G (op (j.unop + c)) ≫ b j.unop = _
    rw [← Category.assoc, limMap_π, Category.assoc, hφb]
    simp [tr]
  · apply limit.hom_ext
    intro j
    rw [Category.assoc, limMap_π, ← Category.assoc, hi j.unop]
    change (limit.π G (op (j.unop + c)) ≫ b j.unop) ≫ φ.app j = _
    rw [Category.assoc, hbφ]
    simp [tr]

universe u v

abbrev HasAdicComparison {A : Type u} [CommRing A] (I : Ideal A)
    (E : Type v) [AddCommGroup E] [Module A E]
    (En : ℕ → Type v) [∀ n, AddCommGroup (En n)] [∀ n, Module A (En n)] : Prop :=
  ∃ (t : ∀ m n, n ≤ m → En m →ₗ[A] En n)
    (r : ∀ n, E →ₗ[A] En n)
    (f : ∀ n, (E ⧸ I ^ n • (⊤ : Submodule A E)) →ₗ[A] En n),
    (∀ n, t n n le_rfl = LinearMap.id) ∧
    (∀ k m n (hkm : m ≤ k) (hmn : n ≤ m), (t m n hmn).comp (t k m hkm) =
      t k n (hmn.trans hkm)) ∧
    (∀ m n (h : n ≤ m), (t m n h).comp (r m) = r n) ∧
    (∀ n, (f n).comp (I ^ n • (⊤ : Submodule A E)).mkQ = r n) ∧
    (∀ m n (h : n ≤ m), (t m n h).comp (f m) =
      (f n).comp (Submodule.factorPow I E h)) ∧
    let Qs := Functor.ofOpSequence
      (X := fun n => ModuleCat.of A (E ⧸ I ^ n • (⊤ : Submodule A E)))
      (fun n => ModuleCat.ofHom (Submodule.factorPowSucc I E n))
    let Es := Functor.ofOpSequence (X := fun n => ModuleCat.of A (En n))
      (fun n => ModuleCat.ofHom (t (n + 1) n n.le_succ))
    ∃ e : limit Qs ≅ limit Es, ∀ n, e.hom ≫ limit.π Es (op n) =
      limit.π Qs (op n) ≫ ModuleCat.ofHom (f n)

private lemma transition_quotients {A : Type u} [CommRing A] (I : Ideal A)
    (E : Type v) [AddCommGroup E] [Module A E] {m n : ℕ} (h : n ≤ m) :
    tr (Functor.ofOpSequence
      (X := fun n => ModuleCat.of A (E ⧸ I ^ n • (⊤ : Submodule A E)))
      (fun n => ModuleCat.ofHom (Submodule.factorPowSucc I E n))) h =
      ModuleCat.ofHom (Submodule.factorPow I E h) := by
  induction m, h using Nat.le_induction with
  | base =>
    unfold tr
    rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    ext ⟨x⟩
    rfl
  | succ m h ih =>
    rw [← ProIso.tr_trans _ h (Nat.le_succ m), ih]
    simp only [tr, Functor.ofOpSequence_map_homOfLE_succ]
    ext ⟨x⟩
    rfl

-- Transporting both systems requires simultaneous quotient and limit constructions.
set_option backward.isDefEq.respectTransparency false in
private lemma adicComparison_of_systems {A : Type u} [CommRing A] (I : Ideal A)
    (E : Type v) [AddCommGroup E] [Module A E]
    (En : ℕ → Type v) [∀ n, AddCommGroup (En n)] [∀ n, Module A (En n)]
    (F G : ℕᵒᵖ ⥤ ModuleCat.{v} A) (φ : F ⟶ G) [IsIso (limMap φ)]
    (q : ∀ n, F.obj (op n) ≅ ModuleCat.of A (E ⧸ I ^ n • (⊤ : Submodule A E)))
    (hq : ∀ n, tr F (Nat.le_succ n) ≫ (q n).hom =
      (q (n + 1)).hom ≫ ModuleCat.ofHom (Submodule.factorPowSucc I E n))
    (e : ∀ n, G.obj (op n) ≅ ModuleCat.of A (En n)) :
    HasAdicComparison I E En := by
  let Qs := Functor.ofOpSequence
    (X := fun n => ModuleCat.of A (E ⧸ I ^ n • (⊤ : Submodule A E)))
    (fun n => ModuleCat.ofHom (Submodule.factorPowSucc I E n))
  let qNat : F ⟶ Qs := NatTrans.ofOpSequence (fun n => (q n).hom) (by
    intro n
    simpa [Qs, tr] using hq n)
  let qIso : F ≅ Qs := NatIso.ofComponents (fun j => q j.unop) (by
    intro i j f
    exact qNat.naturality f)
  let t (m n : ℕ) (h : n ≤ m) := ((e m).inv ≫ tr G h ≫ (e n).hom).hom
  let Es := Functor.ofOpSequence (X := fun n => ModuleCat.of A (En n))
    (fun n => ModuleCat.ofHom (t (n + 1) n n.le_succ))
  let eNat : G ⟶ Es := NatTrans.ofOpSequence (fun n => (e n).hom) (by
    intro n
    simp [Es, t, tr])
  let eIso : G ≅ Es := NatIso.ofComponents (fun j => e j.unop) (by
    intro i j f
    exact eNat.naturality f)
  let f (n : ℕ) := ((q n).inv ≫ φ.app (op n) ≫ (e n).hom).hom
  have hfn (m n : ℕ) (h : n ≤ m) :
      (t m n h).comp (f m) = (f n).comp (Submodule.factorPow I E h) := by
    have hn := (qIso.inv ≫ φ ≫ eNat).naturality (homOfLE h).op
    have ht : tr Es h = (e m).inv ≫ tr G h ≫ (e n).hom := by
      have he := eNat.naturality (homOfLE h).op
      apply (cancel_epi (e m).hom).mp
      rw [Iso.hom_inv_id_assoc]
      exact he.symm
    change tr Qs h ≫ ((q n).inv ≫ φ.app (op n) ≫ (e n).hom) =
      ((q m).inv ≫ φ.app (op m) ≫ (e m).hom) ≫ tr Es h at hn
    rw [show tr Qs h = ModuleCat.ofHom (Submodule.factorPow I E h) from
      transition_quotients I E h, ht] at hn
    exact (congrArg ModuleCat.Hom.hom hn).symm
  refine ⟨t, fun n => (f n).comp (I ^ n • (⊤ : Submodule A E)).mkQ, f,
    ?_, ?_, ?_, fun n => rfl, hfn, ?_⟩
  · intro n
    ext x
    simp [t, tr]
  · intro k m n hkm hmn
    apply ModuleCat.hom_ext_iff.mp
    change ((e k).inv ≫ tr G hkm ≫ (e m).hom) ≫
        ((e m).inv ≫ tr G hmn ≫ (e n).hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (tr G hkm), ProIso.tr_trans]
  · intro m n h
    rw [← LinearMap.comp_assoc, hfn, LinearMap.comp_assoc]
    congr 1
  · let l := (HasLimit.isoOfNatIso qIso).symm ≪≫ asIso (limMap φ) ≪≫
      HasLimit.isoOfNatIso eIso
    refine ⟨l, ?_⟩
    intro n
    change l.hom ≫ limit.π Es (op n) = limit.π Qs (op n) ≫ _
    dsimp only [l, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [Category.assoc, Category.assoc, HasLimit.isoOfNatIso_hom_π,
      ← Category.assoc (limMap φ), limMap_π, ← Category.assoc,
      ← Category.assoc (HasLimit.isoOfNatIso qIso).inv, HasLimit.isoOfNatIso_inv_π]
    rfl

end Limits

section QuotientEquivalences

private def quotientEquivMapIdeal {A B H E : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup H] [Module B H] [Module A H] [IsScalarTower A B H]
    [AddCommGroup E] [Module B E] [Module A E] [IsScalarTower A B E]
    (I : Ideal A) (e : H ≃ₗ[B] E) :
    (H ⧸ I.map (algebraMap A B) • (⊤ : Submodule B H)) ≃ₗ[A]
      (E ⧸ I • (⊤ : Submodule A E)) :=
  ((Submodule.Quotient.equiv
      (I.map (algebraMap A B) • (⊤ : Submodule B H))
      (I.map (algebraMap A B) • (⊤ : Submodule B E)) e (by
        rw [Submodule.map_smul'', Submodule.map_top, e.range])).restrictScalars A).trans
    ((Submodule.Quotient.restrictScalarsEquiv A
      (I.map (algebraMap A B) • (⊤ : Submodule B E))).symm.trans
        (Submodule.quotEquivOfEq _ _ (by
          rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top])))

private lemma quotientEquivMapIdeal_mk {A B H E : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup H] [Module B H] [Module A H] [IsScalarTower A B H]
    [AddCommGroup E] [Module B E] [Module A E] [IsScalarTower A B E]
    (I : Ideal A) (e : H ≃ₗ[B] E) (x : H) :
    quotientEquivMapIdeal I e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

universe uR uM uV

def quotientULiftEquiv {R : Type uR} [CommRing R]
    (I : Ideal R) (M : Type uM) [AddCommGroup M] [Module R M] :
    ((ULift.{uV} M) ⧸ I • (⊤ : Submodule R (ULift.{uV} M))) ≃ₗ[R ⧸ I]
      ULift.{uV} (M ⧸ I • (⊤ : Submodule R M)) :=
  ((Submodule.Quotient.equiv _ _ (ULift.moduleEquiv : ULift.{uV} M ≃ₗ[R] M)
      (by rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).trans
    ULift.moduleEquiv.symm).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

end QuotientEquivalences

section HomologyComparison

-- `tr` comes from the untagged `InverseSequence` replay in `AdicSystem/Homology.lean`.
open InverseSequence

universe uA uB v

-- The comparison combines the Artin–Rees inverse maps with restriction of scalars.
set_option backward.isDefEq.respectTransparency false in
lemma adicComparison_of_complex
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B]
    {K L T E : Type v} [AddCommGroup K] [Module B K] [Module.Finite B K]
    [AddCommGroup L] [Module B L] [Module.Finite B L]
    [AddCommGroup T] [Module B T] [Module.Finite B T]
    [AddCommGroup E] [Module B E] [Module A E] [IsScalarTower A B E]
    (En : ℕ → Type v) [∀ n, AddCommGroup (En n)] [∀ n, Module B (En n)]
    [∀ n, Module A (En n)] [∀ n, IsScalarTower A B (En n)]
    (I : Ideal A) (α : K →ₗ[B] L) (β : L →ₗ[B] T) (hαβ : β.comp α = 0) :
    let J := I.map (algebraMap A B)
    let H := β.ker ⧸ α.range.comap β.ker.subtype
    let Z (n : ℕ) := (J ^ n • (⊤ : Submodule B T)).comap β
    let Hn (n : ℕ) := Z n ⧸ (α.range ⊔ J ^ n • (⊤ : Submodule B L)).comap (Z n).subtype
    (H ≃ₗ[B] E) → (∀ n, Hn n ≃ₗ[B] En n) → HasAdicComparison I E En := by
  dsimp only
  intro e en
  let J := I.map (algebraMap A B)
  let H := β.ker ⧸ α.range.comap β.ker.subtype
  let Z (n : ℕ) := (J ^ n • (⊤ : Submodule B T)).comap β
  let Hn (n : ℕ) := Z n ⧸ (α.range ⊔ J ^ n • (⊤ : Submodule B L)).comap (Z n).subtype
  obtain ⟨tl, t, qt, f, _, _, hqt, ht, hf, c, _, b, hb₁, hb₂, _⟩ :=
    Stacks.AdicSystem.ArtinReesHomology.exists_uniform_adic_homology_comparison J α β hαβ
  have hfn (n : ℕ) : (t n).comp (f (n + 1)) = (f n).comp (qt n) := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hf' (k : ℕ) (x : H) : f k (Submodule.Quotient.mk x) = tl k x :=
        LinearMap.congr_fun (hf k) x
      simp only [LinearMap.comp_apply, hf', hqt]
      exact LinearMap.congr_fun (ht n) x
  let Fs := Functor.ofOpSequence
    (X := fun n => ModuleCat.of B (H ⧸ J ^ n • (⊤ : Submodule B H)))
    (fun n => ModuleCat.ofHom (qt n))
  let Gs := Functor.ofOpSequence (X := fun n => ModuleCat.of B (Hn n))
    (fun n => ModuleCat.ofHom (t n))
  let R := ModuleCat.restrictScalars (algebraMap A B)
  let F := Fs ⋙ R
  let G := Gs ⋙ R
  let φ : F ⟶ G := NatTrans.ofOpSequence (fun n => R.map (ModuleCat.ofHom (f n))) (by
    intro n
    change R.map (Fs.map _) ≫ R.map (ModuleCat.ofHom (f n)) =
      R.map (ModuleCat.ofHom (f (n + 1))) ≫ R.map (Gs.map _)
    simp only [Fs, Gs, Functor.ofOpSequence_map_homOfLE_succ, ← R.map_comp]
    exact congrArg R.map (ModuleCat.hom_ext (hfn n).symm))
  have hshift (n : ℕ) : ∃ b' : G.obj (op (n + c)) ⟶ F.obj (op n),
      b' ≫ φ.app (op n) = tr G (Nat.le_add_right n c) ∧
      φ.app (op (n + c)) ≫ b' = tr F (Nat.le_add_right n c) := by
    have hb : ∀ hn : n + c - c ≤ n + c,
        ∃ b' : G.obj (op (n + c)) ⟶ F.obj (op (n + c - c)),
          b' ≫ φ.app (op (n + c - c)) = tr G hn ∧
          φ.app (op (n + c)) ≫ b' = tr F hn := by
      intro hn
      refine ⟨R.map (ModuleCat.ofHom (b (n + c) (Nat.le_add_left c n))), ?_, ?_⟩
      · exact congrArg R.map (ModuleCat.hom_ext (hb₂ (n + c) (Nat.le_add_left c n)))
      · exact congrArg R.map (ModuleCat.hom_ext (hb₁ (n + c) (Nat.le_add_left c n)))
    rw [Nat.add_sub_cancel] at hb
    exact hb (Nat.le_add_right n c)
  choose b' hbφ hφb using hshift
  obtain ⟨l, hl⟩ := exists_limitIso_of_shift_inverse F G φ c b' hbφ hφb
  have hl' : limMap φ = l.hom := by
    apply limit.hom_ext
    intro j
    exact (limMap_π φ j).trans (hl j.unop).symm
  have : IsIso (limMap φ) := hl' ▸ inferInstance
  let : Module A H := Module.compHom H (algebraMap A B)
  let : IsScalarTower A B H := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let q (n : ℕ) : (H ⧸ J ^ n • (⊤ : Submodule B H)) ≃ₗ[A]
      (E ⧸ I ^ n • (⊤ : Submodule A E)) :=
    ((Submodule.quotEquivOfEq _ _ (by rw [Ideal.map_pow])).restrictScalars A).trans
      (quotientEquivMapIdeal (I ^ n) e)
  let (n : ℕ) : Module A (Hn n) := Module.compHom (Hn n) (algebraMap A B)
  let (n : ℕ) : IsScalarTower A B (Hn n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  apply adicComparison_of_systems I E En F G φ
    (fun n => (q n).toModuleIso) _ (fun n => ((en n).restrictScalars A).toModuleIso)
  intro n
  change R.map (Fs.map _) ≫ _ = _
  simp only [Fs, Functor.ofOpSequence_map_homOfLE_succ]
  apply ModuleCat.hom_ext
  ext ⟨x⟩
  change q n (qt n (Submodule.Quotient.mk x)) =
    Submodule.factorPowSucc I E n (q (n + 1) (Submodule.Quotient.mk x))
  rw [hqt]
  have hq (k : ℕ) : q k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := by
    rfl
  rw [hq, hq]
  rfl

end HomologyComparison

end Stacks.AdicSystem.ExtFlatBaseChange

end

end

end
