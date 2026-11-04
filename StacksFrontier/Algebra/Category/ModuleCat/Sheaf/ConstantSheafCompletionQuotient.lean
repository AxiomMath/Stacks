module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletion
public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
import StacksCore.Tactic.StacksAttribute

/-!
# The completed constant sheaf modulo the completed constant ideal sheaf

Let `J` be a Grothendieck topology on `C`, let `R` be a commutative ring and let `I` be an ideal
of `R`. This file identifies the quotient of the completed constant sheaf `R̲^∧ = lim (R/Iⁿ)̲` by
the completed constant ideal sheaf `I̲^∧ = lim (I/Iⁿ)̲` with the constant sheaf `(R/I)̲`.

## Main definitions

* `Stacks.ConstantSheaf.adicResidueSystem`: the inverse system `n ↦ R/(I + Iⁿ)` of `R`-modules,
  with `Stacks.ConstantSheaf.adicResidueCone` the cone on it with vertex `R/I` and
  `Stacks.ConstantSheaf.adicResidueProjection` the quotient maps from `n ↦ R/Iⁿ`.
* `Stacks.ConstantSheaf.completedConstantSheafResidueMap`: the canonical map `R̲^∧ ⟶ (R/I)̲`.
* `Stacks.ConstantSheaf.completedConstantIdealShortComplex`: the short complex
  `I̲^∧ ⟶ R̲^∧ ⟶ (R/I)̲`.

## Main results

* `Stacks.Sheaf.shortExact_of_sections_shortExact`: a short complex of sheaves which is short
  exact on the sections over every object of the site is short exact.
* `Stacks.ConstantSheaf.shortExact_map_constantSections`: `M ↦ Γ(U, M̲)` takes a short exact
  sequence to a short exact sequence.
* `Stacks.ConstantSheaf.shortExact_completedConstantIdealShortComplex`: the sequence
  `0 → I̲^∧ → R̲^∧ → (R/I)̲ → 0` is short exact.
* `Stacks.ConstantSheaf.completedConstantSheaf_quotientByCompletedIdeal` and
  `Stacks.ConstantSheaf.completedConstantSheaf_quotientByCompletedIdeal_hom_comp`: the
  identification `R̲^∧/I̲^∧ = (R/I)̲`, by an isomorphism carrying the cokernel projection to the
  canonical map `R̲^∧ ⟶ (R/I)̲`.

## References

* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Limits

/-- A functor preserving zero morphisms takes a zero object to a zero object. -/
theorem isZero_obj_of_isZero {A : Type*} [Category A] [HasZeroMorphisms A] {B : Type*}
    [Category B] [HasZeroMorphisms B] (F : A ⥤ B) [F.PreservesZeroMorphisms] {X : A}
    (hX : IsZero X) : IsZero (F.obj X) :=
  F.map_isZero hX

/-- A cone over a tower whose term at `0` is a zero object and whose legs at the positive indices
are isomorphisms is a limit cone. -/
noncomputable def isLimit_of_isZero_obj_zero {A : Type u} [Category.{v} A] (D : ℕᵒᵖ ⥤ A)
    (c : Cone D)
    (hzero : IsZero (D.obj (op 0))) (hiso : ∀ n : ℕ, 1 ≤ n → IsIso (c.π.app (op n))) :
    IsLimit c := by
  have h1 : IsIso (c.π.app (op 1)) := hiso 1 le_rfl
  have hstep : ∀ (n : ℕ) (hn : 1 ≤ n),
      IsIso (D.map ((homOfLE hn).op : (op n : ℕᵒᵖ) ⟶ op 1)) := by
    intro n hn
    have hi := hiso n hn
    have he : D.map ((homOfLE hn).op : (op n : ℕᵒᵖ) ⟶ op 1) =
        inv (c.π.app (op n)) ≫ c.π.app (op 1) := by
      rw [← c.w ((homOfLE hn).op : (op n : ℕᵒᵖ) ⟶ op 1)]
      simp
    rw [he]
    infer_instance
  refine { lift := fun s => s.π.app (op 1) ≫ inv (c.π.app (op 1)), fac := ?_, uniq := ?_ }
  · intro s j
    obtain ⟨m⟩ := j
    cases m with
    | zero => exact hzero.eq_of_tgt _ _
    | succ m =>
      have hn : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      have hi := hstep (m + 1) hn
      rw [← cancel_mono (D.map ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1)),
        Category.assoc, c.w ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1),
        s.w ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1)]
      simp
  · intro s m hm
    rw [← hm (op 1)]
    simp

end Stacks.Limits

namespace Stacks.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A short complex of sheaves which is short exact on the sections over every object of the site
is short exact. -/
theorem shortExact_of_sections_shortExact {A : Type*} [Category A] [Abelian A]
    [HasSheafify J A] (S : ShortComplex (_root_.CategoryTheory.Sheaf J A))
    (h : ∀ U : Cᵒᵖ, (S.map ((sheafSections J A).obj U)).ShortExact) : S.ShortExact := by
  have hmono : Mono S.f := by
    have : ∀ U : Cᵒᵖ, Mono (((sheafToPresheaf J A).map S.f).app U) := fun U => (h U).mono_f
    exact (sheafToPresheaf J A).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  have hcancel : ∀ {X Y Z : _root_.CategoryTheory.Sheaf J A} (p : X ⟶ Y) (β γ : Y ⟶ Z),
      (∀ U : Cᵒᵖ, Epi (((sheafSections J A).obj U).map p)) → p ≫ β = p ≫ γ → β = γ := by
    intro X Y Z p β γ hp hβγ
    apply _root_.CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have := hp U
    have h2 := congrArg ((sheafSections J A).obj U).map hβγ
    rw [Functor.map_comp, Functor.map_comp] at h2
    exact (cancel_epi (((sheafSections J A).obj U).map p)).mp h2
  have hepi : Epi S.g :=
    ⟨fun β γ hβγ => hcancel S.g β γ (fun U => (h U).epi_g) hβγ⟩
  refine ShortComplex.ShortExact.mk' (S.exact_iff_epi_kernel_lift.mpr ?_) hmono hepi
  refine ⟨fun β γ hβγ => hcancel _ β γ (fun U => ?_) hβγ⟩
  set E := (sheafSections J A).obj U with hE
  have hpl : PreservesFiniteLimits E := by
    rw [hE]
    exact comp_preservesFiniteLimits (sheafToPresheaf J A) ((evaluation _ _).obj U)
  have hek : Epi (kernel.lift (E.map S.g) (E.map S.f) (S.map E).zero) :=
    (h U).exact.epi_kernelLift
  have hcomp : Epi (E.map (kernel.lift S.g S.f S.zero) ≫ kernelComparison S.g E) := by
    rw [map_lift_kernelComparison]
    infer_instance
  exact (epi_comp_iff_of_isIso (E.map (kernel.lift S.g S.f S.zero)) (kernelComparison S.g E)).mp
    hcomp

end Stacks.Sheaf

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type w} [CommRing R] (I : Ideal R)

/-! ### Sections of a constant sheaf take short exact sequences to short exact sequences -/

section Exact

variable [HasSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [J.PreservesSheafification (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]

/-- The functor `M ↦ Γ(U, M̲)` of sections of a constant sheaf of modules takes a short exact
sequence of `R`-modules to a short exact sequence. -/
theorem shortExact_map_constantSections (U : C) (T : ShortComplex (ModuleCat.{w} R))
    (hT : T.ShortExact) : (T.map (constantSections J U)).ShortExact := by
  have hmono : Mono (T.map (constantSections J U)).f := by
    rw [ModuleCat.mono_iff_injective]
    exact injective_constantSections_map J T.f ((ModuleCat.mono_iff_injective _).1 hT.mono_f) U
  have hepi : Epi (T.map (constantSections J U)).g := by
    rw [ModuleCat.epi_iff_surjective]
    exact surjective_constantSections_map J T.g ((ModuleCat.epi_iff_surjective _).1 hT.epi_g) U
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact range_constantSections_map_eq_ker J U T.f T.g
    (T.moduleCat_exact_iff_range_eq_ker.1 hT.exact)

end Exact

/-! ### The tower `n ↦ R/(I + Iⁿ)` -/

/-- The inverse system `n ↦ R/(I + Iⁿ)` of `R`-modules, with the canonical quotient maps as
transition maps. For `n ≥ 1` the ideal `Iⁿ` is contained in `I`, so the term is `R/I`; at `n = 0`
it is zero. -/
noncomputable def adicResidueSystem : ℕᵒᵖ ⥤ ModuleCat.{w} R where
  obj n := ModuleCat.of R (R ⧸ (I + I ^ n.unop))
  map {i j} hij := ModuleCat.ofHom <|
    (I + I ^ i.unop).mapQ (I + I ^ j.unop) LinearMap.id (by
      simpa using sup_le_sup_left (Ideal.pow_le_pow_right (leOfHom hij.unop)) I)
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    simp

/-- The quotient maps `R/Iⁿ ⟶ R/(I + Iⁿ)` as a morphism of inverse systems. -/
noncomputable def adicResidueProjection : adicQuotientSystem I ⟶ adicResidueSystem I where
  app n := ModuleCat.ofHom <|
    (I ^ n.unop).mapQ (I + I ^ n.unop) LinearMap.id (by simp)
  naturality := by
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    rfl

/-- The quotient map `R/I ⟶ R/(I + Iⁿ)`, the `n`-th leg of the cone on the residue tower with
vertex `R/I`. -/
noncomputable def adicResidueConeLeg (n : ℕᵒᵖ) :
    ModuleCat.of R (R ⧸ I) ⟶ (adicResidueSystem I).obj n :=
  ModuleCat.ofHom (I.mapQ (I + I ^ n.unop) LinearMap.id (by simp))

/-- The cone on `n ↦ R/(I + Iⁿ)` with vertex `R/I`, whose legs are the quotient maps. -/
noncomputable def adicResidueCone : Cone (adicResidueSystem I) where
  pt := ModuleCat.of R (R ⧸ I)
  π :=
    { app := fun n => adicResidueConeLeg I n
      naturality := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on
        rfl }

/-- The `n`-th leg of `adicResidueCone I` is the quotient map `adicResidueConeLeg I n`. -/
theorem adicResidueCone_π_app (n : ℕᵒᵖ) :
    (adicResidueCone I).π.app n = adicResidueConeLeg I n :=
  rfl

/-- The identification `R/I¹ = R/I` of the first level of the adic quotient tower with the
quotient by `I`, as the quotient map it is. -/
noncomputable def adicQuotientOneMap :
    (adicQuotientSystem I).obj (op 1) ⟶ ModuleCat.of R (R ⧸ I) :=
  ModuleCat.ofHom ((I ^ 1).mapQ I LinearMap.id (by simp))

/-- The composite `R/Iⁿ ⟶ R/I¹ ⟶ R/I ⟶ R/(I + Iⁿ)` is the quotient map `R/Iⁿ ⟶ R/(I + Iⁿ)`,
for `n ≥ 1`. -/
theorem adicQuotient_map_comp_residueCone_app (n : ℕ) (hn : 1 ≤ n) :
    (adicQuotientSystem I).map ((homOfLE hn).op : (op n : ℕᵒᵖ) ⟶ op 1) ≫
        adicQuotientOneMap I ≫ adicResidueConeLeg I (op n) =
      (adicResidueProjection I).app (op n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on
  rfl

/-- At `n = 0` the term `R/(I + I⁰)` of the residue tower is zero. -/
theorem isZero_adicResidueSystem_obj_zero :
    IsZero ((adicResidueSystem I).obj (op 0)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      refine (Submodule.Quotient.eq _).2 ?_
      have htop : I + I ^ (0 : ℕ) = ⊤ := by simp
      rw [htop]
      exact Submodule.mem_top

/-- A linear map between quotients of the same module sending `mk a` to `mk a` is surjective. -/
private theorem surjective_of_map_mk {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (f : M ⧸ p →ₗ[R] M ⧸ q)
    (hf : ∀ a, f (Submodule.Quotient.mk a) = Submodule.Quotient.mk a) : Function.Surjective f := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ a => exact ⟨Submodule.Quotient.mk a, hf a⟩

/-- For `n ≥ 1` the leg `R/I ⟶ R/(I + Iⁿ)` of the residue cone is bijective. -/
theorem bijective_adicResidueConeLeg (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (adicResidueConeLeg I (op n)).hom := by
  have hIn : I + I ^ n = I := sup_eq_left.2 (Ideal.pow_le_self (by omega))
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      have ha : a ∈ I + I ^ n := (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.mem_ker.1 hx)
      exact (Submodule.Quotient.mk_eq_zero _).2 (hIn ▸ ha)
  · exact surjective_of_map_mk _ fun _ => rfl

/-- The short complex of inverse systems `0 → I/(I ∩ Iⁿ) → R/Iⁿ → R/(I + Iⁿ) → 0`. -/
noncomputable def adicIdealTower : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{w} R) :=
  ShortComplex.mk (adicIdealQuotientInclusion I) (adicResidueProjection I) (by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact Submodule.mem_sup_left a.2)

/-- Every level of the tower of short exact sequences
`0 → I/(I ∩ Iⁿ) → R/Iⁿ → R/(I + Iⁿ) → 0` is short exact. -/
theorem shortExact_adicIdealTower_app (n : ℕᵒᵖ) :
    ((adicIdealTower I).map ((evaluation ℕᵒᵖ (ModuleCat.{w} R)).obj n)).ShortExact := by
  have hmono : Mono (((adicIdealTower I).map
      ((evaluation ℕᵒᵖ (ModuleCat.{w} R)).obj n)).f) := by
    rw [ModuleCat.mono_iff_injective, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      have hx' : (Submodule.Quotient.mk (a : R) : R ⧸ I ^ n.unop) = 0 :=
        LinearMap.mem_ker.1 hx
      have ha : (a : R) ∈ I ^ n.unop := (Submodule.Quotient.mk_eq_zero (I ^ n.unop)).1 hx'
      exact (Submodule.Quotient.mk_eq_zero _).2 ha
  have hepi : Epi (((adicIdealTower I).map
      ((evaluation ℕᵒᵖ (ModuleCat.{w} R)).obj n)).g) := by
    rw [ModuleCat.epi_iff_surjective]
    exact surjective_of_map_mk _ fun _ => rfl
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    induction y using Submodule.Quotient.induction_on with
    | _ a =>
      refine LinearMap.mem_ker.2 ?_
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_sup_left a.2)
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      have ha : a ∈ I + I ^ n.unop :=
        (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.mem_ker.1 hx)
      obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      refine (Submodule.Quotient.eq _).2 ?_
      simpa using Submodule.neg_mem _ hc

/-! ### The identification `R̲^∧/I̲^∧ = (R/I)̲` -/

section Quotient

variable [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The constant sheaf functor `constantSheaf J (ModuleCat R)` is additive. -/
instance constantSheaf_additive :
    (constantSheaf J (ModuleCat.{w} R)).Additive :=
  inferInstanceAs (Functor.Additive (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{w} R)))

/-- The canonical map `R̲^∧ ⟶ (R/I)̲` from the completed constant sheaf to the constant sheaf of
the quotient ring: the projection to the level `n = 1` of the completion, followed by the
identification `R/I¹ = R/I`. -/
@[stacks 093M "the canonical map from the completion to the constant sheaf of Λ/I"]
noncomputable def completedConstantSheafResidueMap :
    completedConstantSheaf J I ⟶
      (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I)) :=
  completedConstantSheafπ J I (op 1) ≫
    (constantSheaf J (ModuleCat.{w} R)).map (adicQuotientOneMap I)

/-- The canonical map `R̲^∧ ⟶ (R/I)̲` sits over the residue tower below the projection from the
tower `n ↦ (R/Iⁿ)̲`. -/
theorem completedConstantSheafResidueMap_comp_residueCone (n : ℕᵒᵖ) :
    completedConstantSheafResidueMap J I ≫ (constantSheaf J (ModuleCat.{w} R)).map
        (adicResidueConeLeg I n) =
      completedConstantSheafπ J I n ≫ (constantSheaf J (ModuleCat.{w} R)).map
        ((adicResidueProjection I).app n) := by
  obtain ⟨m⟩ := n
  cases m with
  | zero =>
    exact (Stacks.Limits.isZero_obj_of_isZero (constantSheaf J (ModuleCat.{w} R))
      (isZero_adicResidueSystem_obj_zero I)).eq_of_tgt _ _
  | succ m =>
    have hn : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have hw : completedConstantSheafπ J I (op (m + 1)) ≫
        (constantSheaf J (ModuleCat.{w} R)).map ((adicQuotientSystem I).map
          ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1)) =
        completedConstantSheafπ J I (op 1) :=
      limit.w (adicQuotientSheafSystem J I) ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1)
    calc completedConstantSheafResidueMap J I ≫
          (constantSheaf J (ModuleCat.{w} R)).map (adicResidueConeLeg I (op (m + 1)))
        = completedConstantSheafπ J I (op 1) ≫ (constantSheaf J (ModuleCat.{w} R)).map
            (adicQuotientOneMap I ≫ adicResidueConeLeg I (op (m + 1))) := by
          rw [completedConstantSheafResidueMap, Category.assoc, ← Functor.map_comp]
      _ = (completedConstantSheafπ J I (op (m + 1)) ≫ (constantSheaf J (ModuleCat.{w} R)).map
            ((adicQuotientSystem I).map ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1))) ≫
            (constantSheaf J (ModuleCat.{w} R)).map
              (adicQuotientOneMap I ≫ adicResidueConeLeg I (op (m + 1))) := by
          rw [← hw]
      _ = completedConstantSheafπ J I (op (m + 1)) ≫ (constantSheaf J (ModuleCat.{w} R)).map
            ((adicQuotientSystem I).map ((homOfLE hn).op : (op (m + 1) : ℕᵒᵖ) ⟶ op 1) ≫
              adicQuotientOneMap I ≫ adicResidueConeLeg I (op (m + 1))) := by
          rw [Category.assoc, ← Functor.map_comp]
      _ = completedConstantSheafπ J I (op (m + 1)) ≫ (constantSheaf J (ModuleCat.{w} R)).map
            ((adicResidueProjection I).app (op (m + 1))) := by
          rw [adicQuotient_map_comp_residueCone_app I (m + 1) hn]

/-- The short complex `I̲^∧ ⟶ R̲^∧ ⟶ (R/I)̲`. -/
noncomputable def completedConstantIdealShortComplex :
    ShortComplex (Sheaf J (ModuleCat.{w} R)) :=
  ShortComplex.mk (completedConstantIdealSheafInclusion J I)
    (completedConstantSheafResidueMap J I) (by
      rw [completedConstantSheafResidueMap, ← Category.assoc,
        completedConstantIdealSheafInclusion_π, Category.assoc, ← Functor.map_comp]
      have hz : (adicIdealQuotientInclusion I).app (op 1) ≫ adicQuotientOneMap I = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | _ a =>
          refine (Submodule.Quotient.mk_eq_zero _).2 ?_
          exact a.2
      rw [hz, Functor.map_zero, comp_zero])

section Sections

variable [HasSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]
  [J.PreservesSheafification (forget (ModuleCat.{w} R))]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]

/-- The short complex of towers of sections
`0 → Γ(U, (I/(I ∩ Iⁿ))̲) → Γ(U, (R/Iⁿ)̲) → Γ(U, (R/(I + Iⁿ))̲) → 0`. -/
noncomputable def adicIdealSectionsTower (U : C) : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{w} R) :=
  (adicIdealTower I).map
    ((Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{w} R) (ModuleCat.{w} R)).obj
      (constantSections J U))

/-- Every level of the tower of sections is short exact. -/
theorem shortExact_adicIdealSectionsTower_app (U : C) (n : ℕᵒᵖ) :
    ((adicIdealSectionsTower J I U).map
      ((evaluation ℕᵒᵖ (ModuleCat.{w} R)).obj n)).ShortExact :=
  shortExact_map_constantSections J U _ (shortExact_adicIdealTower_app I n)

omit [HasSheafify J (ModuleCat.{w} R)] in
/-- The tower of sections of the constant sheaves on `I/(I ∩ Iⁿ)` satisfies the Mittag-Leffler
condition. -/
theorem isMittagLeffler_adicIdealSectionsTower (U : C) :
    ((adicIdealSectionsTower J I U).X₁ ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler := by
  have hsurj : ∀ {i j : ℕᵒᵖ} (hij : i ⟶ j),
      Function.Surjective ((adicIdealSectionsTower J I U).X₁.map hij).hom := by
    intro i j hij
    exact surjective_constantSections_map J ((adicIdealQuotientSystem I).map hij)
      (surjective_of_map_mk _ fun _ => rfl) U
  refine (Functor.isMittagLeffler_iff_subset_range_comp _).2 fun j => ?_
  refine ⟨j, 𝟙 j, fun k g => ?_⟩
  intro y _
  exact hsurj (g ≫ 𝟙 j) y

/-- The cone on the residue tower of sections with vertex `Γ(U, (R/I)̲)`, whose legs are the
sections of the quotient maps `R/I ⟶ R/(I + Iⁿ)`. -/
noncomputable def adicResidueSectionsCone (U : C) :
    Cone (adicResidueSystem I ⋙ constantSections J U) where
  pt := ((sheafSections J (ModuleCat.{w} R)).obj (op U)).obj
    ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I)))
  π :=
    { app := fun n => (constantSections J U).map (adicResidueConeLeg I n)
      naturality := by
        intro i j hij
        have h : adicResidueConeLeg I i ≫ (adicResidueSystem I).map hij =
            adicResidueConeLeg I j := (adicResidueCone I).w hij
        change (𝟙 _) ≫ (constantSections J U).map (adicResidueConeLeg I j) =
          (constantSections J U).map (adicResidueConeLeg I i) ≫
            (constantSections J U).map ((adicResidueSystem I).map hij)
        rw [Category.id_comp, ← Functor.map_comp, h] }

/-- The cone with vertex `Γ(U, (R/I)̲)` exhibits `Γ(U, (R/I)̲)` as the inverse limit of the
residue tower of sections. -/
noncomputable def isLimit_adicResidueSectionsCone (U : C) :
    IsLimit (adicResidueSectionsCone J I U) := by
  refine Stacks.Limits.isLimit_of_isZero_obj_zero _ _ ?_ ?_
  · exact Stacks.Limits.isZero_obj_of_isZero (constantSections J U)
      (isZero_adicResidueSystem_obj_zero I)
  · intro n hn
    have h1 : IsIso (adicResidueConeLeg I (op n)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_adicResidueConeLeg I n hn)
    exact (inferInstance :
      IsIso ((constantSections J U).map (adicResidueConeLeg I (op n))))

/-- The sections over `U` of the short complex `I̲^∧ ⟶ R̲^∧ ⟶ (R/I)̲` form a short exact
sequence. -/
theorem shortExact_map_completedConstantIdealShortComplex_sections (U : C) :
    ((completedConstantIdealShortComplex J I).map
      ((sheafSections J (ModuleCat.{w} R)).obj (op U))).ShortExact := by
  have hev : PreservesLimitsOfShape ℕᵒᵖ ((sheafSections J (ModuleCat.{w} R)).obj (op U)) :=
    preservesLimitsOfShape_of_natIso
      (sheafSectionsNatIsoEvaluation (J := J) (A := ModuleCat.{w} R) (X := U)).symm
  have hlim := (adicIdealSectionsTower J I U).shortExact_map_lim_of_isMittagLeffler
    (shortExact_adicIdealSectionsTower_app J I U)
    (isMittagLeffler_adicIdealSectionsTower J I U)
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (preservesLimitIso ((sheafSections J (ModuleCat.{w} R)).obj (op U))
      (adicIdealQuotientSheafSystem J I))
    (preservesLimitIso ((sheafSections J (ModuleCat.{w} R)).obj (op U))
      (adicQuotientSheafSystem J I))
    ((isLimit_adicResidueSectionsCone J I U).conePointUniqueUpToIso
      (limit.isLimit (adicResidueSystem I ⋙ constantSections J U))) ?_ ?_).symm hlim
  · exact ((preservesLimitNatIso ((sheafSections J (ModuleCat.{w} R)).obj (op U))).hom.naturality
      (Functor.whiskerRight (adicIdealQuotientInclusion I)
        (constantSheaf J (ModuleCat.{w} R)))).symm
  · refine limit.hom_ext fun n => ?_
    set E := (sheafSections J (ModuleCat.{w} R)).obj (op U) with hE
    set τ₃ := (isLimit_adicResidueSectionsCone J I U).conePointUniqueUpToIso
      (limit.isLimit (adicResidueSystem I ⋙ constantSections J U)) with hτ₃
    have hL : ((preservesLimitIso E (adicQuotientSheafSystem J I)).hom ≫
          limMap (Functor.whiskerRight (adicResidueProjection I) (constantSections J U))) ≫
            limit.π (adicResidueSystem I ⋙ constantSections J U) n =
        E.map (limit.π (adicQuotientSheafSystem J I) n ≫
          (constantSheaf J (ModuleCat.{w} R)).map ((adicResidueProjection I).app n)) := by
      rw [Category.assoc, limMap_π, ← Category.assoc,
        preservesLimitIso_hom_π E (adicQuotientSheafSystem J I) n, Functor.map_comp]
      rfl
    have hleg : τ₃.hom ≫ limit.π (adicResidueSystem I ⋙ constantSections J U) n =
        (constantSections J U).map (adicResidueConeLeg I n) :=
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ n
    have hassoc : (E.map (completedConstantSheafResidueMap J I) ≫ τ₃.hom) ≫
          limit.π (adicResidueSystem I ⋙ constantSections J U) n =
        E.map (completedConstantSheafResidueMap J I) ≫
          (τ₃.hom ≫ limit.π (adicResidueSystem I ⋙ constantSections J U) n) :=
      Category.assoc _ _ _
    have hR : (E.map (completedConstantSheafResidueMap J I) ≫ τ₃.hom) ≫
          limit.π (adicResidueSystem I ⋙ constantSections J U) n =
        E.map (completedConstantSheafResidueMap J I ≫
          (constantSheaf J (ModuleCat.{w} R)).map (adicResidueConeLeg I n)) :=
      hassoc.trans ((congrArg (fun k => E.map (completedConstantSheafResidueMap J I) ≫ k)
        hleg).trans (Functor.map_comp E _ _).symm)
    exact hL.trans
      ((congrArg E.map (completedConstantSheafResidueMap_comp_residueCone J I n).symm).trans
        hR.symm)

/-- The sequence `0 → I̲^∧ → R̲^∧ → (R/I)̲ → 0` of sheaves of `R`-modules is short exact. -/
@[stacks 093M "the completed ideal sheaf is the kernel of the map from the completion to (Λ/I)̲"]
theorem shortExact_completedConstantIdealShortComplex :
    (completedConstantIdealShortComplex J I).ShortExact :=
  Stacks.Sheaf.shortExact_of_sections_shortExact J _ fun U =>
    shortExact_map_completedConstantIdealShortComplex_sections J I U.unop

/-- The canonical isomorphism `R̲^∧/I̲^∧ ≅ (R/I)̲` from the quotient of the completed constant
sheaf by the completed constant ideal sheaf to the constant sheaf of the quotient ring. -/
@[stacks 093M "Λ̂/Î = (Λ/I)̲"]
noncomputable def completedConstantSheaf_quotientByCompletedIdeal :
    cokernel (completedConstantIdealSheafInclusion J I) ≅
      (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R (R ⧸ I)) :=
  (cokernelIsCokernel (completedConstantIdealSheafInclusion J I)).coconePointUniqueUpToIso
    (shortExact_completedConstantIdealShortComplex J I).gIsCokernel

/-- The isomorphism `R̲^∧/I̲^∧ ≅ (R/I)̲` intertwines the cokernel projection with the canonical
map `R̲^∧ ⟶ (R/I)̲`. -/
@[stacks 093M "Λ̂/Î = (Λ/I)̲"]
theorem completedConstantSheaf_quotientByCompletedIdeal_hom_comp :
    cokernel.π (completedConstantIdealSheafInclusion J I) ≫
        (completedConstantSheaf_quotientByCompletedIdeal J I).hom =
      completedConstantSheafResidueMap J I :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (completedConstantIdealSheafInclusion J I))
    (shortExact_completedConstantIdealShortComplex J I).gIsCokernel WalkingParallelPair.one

end Sections

end Quotient

end Stacks.ConstantSheaf

end
