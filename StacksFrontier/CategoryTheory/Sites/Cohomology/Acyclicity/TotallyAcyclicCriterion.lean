module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Coproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.ExtTowerVanishing
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation
public import StacksFrontier.CategoryTheory.Sites.Representable.CoveredByRepresentables
import StacksCore.Tactic.StacksAttribute

/-!
# A criterion for total acyclicity

Let `𝒞` be a site and `𝓕` an abelian sheaf on it. [Stacks, Tag 072Y] calls `𝓕` *totally acyclic*
when `H^p(K, 𝓕) = 0` for every sheaf of sets `K` and every `p ≥ 1`, where `H^p(K, 𝓕)` is `Ext^p`
out of the free abelian sheaf `ℤ_K^♯` (`Stacks.Cohomology.cohomologyOverSheaf`). By
[Stacks, Tag 07A1] this happens exactly when

1. `H^p(U, 𝓕) = 0` for `p > 0` and every object `U` of `𝒞`, and
2. for every surjection `K' → K` of sheaves of sets the extended Čech complex
   `0 → H^0(K, 𝓕) → H^0(K', 𝓕) → H^0(K' ×_K K', 𝓕) → …` is exact.

## Main results

* `Stacks.Cohomology.isTotallyAcyclic_iff`: **[Stacks, Tag 07A1]**, the characterisation.
* `Stacks.Cohomology.isTotallyAcyclic_of_conditions`: conditions (1) and (2) imply total
  acyclicity; only the positive-degree half `CechComplexExactPos` of condition (2) is needed.
* `Stacks.Cohomology.cechComplexExact_iff_cechComplexExactPos`: the two forms of condition (2)
  agree, the degree-zero half holding for every abelian sheaf.
* `Stacks.Cohomology.cechComplexExactPos_of_injective`: condition (2) holds for every injective
  abelian sheaf.
* `Stacks.Cohomology.exists_epi_subsingleton_ext`: under condition (1), every sheaf of sets `K`
  receives a surjection `K' → K` of sheaves of sets with `H^p(K', 𝓕) = 0` for all `p > 0`.

## Implementation notes

Condition (1) is the vanishing of `Ext^p(ℤ_P^♯, 𝓕)` for every presheaf `P` representable by an
object `U`, which is `H^p(U, 𝓕)`. Condition (2) is that the augmentation
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEpsNat` of the Čech Hom complex is a
quasi-isomorphism, for every surjection of sheaves of sets.

## References

* [Stacks Project, Tag 07A1](https://stacks.math.columbia.edu/tag/07A1)
* [Stacks Project, Tag 072Y](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks Project, Tag 079Z](https://stacks.math.columbia.edu/tag/079Z)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
* [Stacks Project, Tag 00WS](https://stacks.math.columbia.edu/tag/00WS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace Stacks.Cohomology

/-! ### `Ext`-vanishing along a short exact sequence -/

section Ext

variable {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]

/-- **`Ext`-vanishing out of an object transports along an isomorphism of that object.** -/
lemma subsingleton_ext_of_iso {X X' Y : A} (e : X ≅ X') (q : ℕ)
    (h : Subsingleton (Abelian.Ext.{w} X' Y q)) : Subsingleton (Abelian.Ext.{w} X Y q) :=
  ⟨fun a b ↦ by
    rw [ColimitsOfCohomology.ext_eq_zero_of_iso_first e q (fun c ↦ h.elim c 0) a,
      ColimitsOfCohomology.ext_eq_zero_of_iso_first e q (fun c ↦ h.elim c 0) b]⟩

variable {S : ShortComplex A} (Y : A)

/-- **`Ext^q` out of the sub-object of a short exact sequence vanishes** as soon as it vanishes
out of the ambient object in the same degree and out of the quotient one degree up. -/
lemma subsingleton_ext_X₁_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (h₂ : Subsingleton (Abelian.Ext.{w} S.X₂ Y q))
    (h₃ : Subsingleton (Abelian.Ext.{w} S.X₃ Y (q + 1))) :
    Subsingleton (Abelian.Ext.{w} S.X₁ Y q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x
    (n₁ := q + 1) (by omega) (h₃.elim _ 0)
  rw [← hx₂, h₂.elim x₂ 0, Abelian.Ext.comp_zero]

/-- **A map out of the sub-object of a short exact sequence extends to the ambient object** as
soon as `Ext^1` out of the quotient vanishes. -/
lemma exists_comp_eq_of_subsingleton_extOne (hS : S.ShortExact)
    (h : Subsingleton (Abelian.Ext.{w} S.X₃ Y 1)) (a : S.X₁ ⟶ Y) :
    ∃ b : S.X₂ ⟶ Y, S.f ≫ b = a := by
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y
    (Abelian.Ext.mk₀.{w} a) (n₁ := 1) (by omega) (h.elim _ 0)
  obtain ⟨b, rfl⟩ := (Abelian.Ext.mk₀_bijective.{w} S.X₂ Y).2 x₂
  rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂
  exact ⟨b, (Abelian.Ext.mk₀_bijective.{w} S.X₁ Y).1 hx₂⟩

end Ext

/-! ### The Čech nerve in degree zero -/

section CechNerve

variable {C : Type u} [SmallCategory C] {K' K : Cᵒᵖ ⥤ Type u}

/-- **Degree zero of a Čech nerve is its source.** The degree-zero term of the Čech nerve of
`f : K' ⟶ K` is `K'`. -/
def cechNerveZeroIso (f : K' ⟶ K) :
    (Arrow.mk f).cechNerve.obj (op (SimplexCategory.mk 0)) ≅ K' where
  hom := WidePullback.π (fun _ : Fin 1 ↦ f) 0
  inv := WidePullback.lift f (fun _ ↦ 𝟙 K') (fun _ ↦ Category.id_comp f)
  hom_inv_id := by
    have : Subsingleton (Fin ((unop (op (SimplexCategory.mk 0))).len + 1)) :=
      inferInstanceAs (Subsingleton (Fin 1))
    refine WidePullback.hom_ext _ _ _ (fun j ↦ ?_) ?_
    · obtain rfl : (0 : Fin ((unop (op (SimplexCategory.mk 0))).len + 1)) = j :=
        Subsingleton.elim _ _
      rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
      rfl
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.π_arrow, Category.id_comp]
      rfl
  inv_hom_id := WidePullback.lift_π (fun _ : Fin 1 ↦ f) _ _ _ 0

end CechNerve

/-! ### The criterion -/

section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- Condition (1) of [Stacks, Tag 07A1]: the cohomology of `F` vanishes in positive degrees on
every object of the site, i.e. `Ext^p` out of the free abelian sheaf on a representable presheaf
of sets vanishes for `p > 0`. -/
def VanishesOnObjects (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  ∀ (U : C) (Q : Cᵒᵖ ⥤ Type u), Q.RepresentableBy U → ∀ p : ℕ, 1 ≤ p →
    Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj Q) F p)

/-- Condition (2) of [Stacks, Tag 07A1]: for every surjection `g : K' ⟶ K` of sheaves of sets the
extended Čech complex `0 → H^0(K, F) → H^0(K', F) → H^0(K' ×_K K', F) → …` is exact, which is the
statement that the augmentation of the Čech Hom complex is a quasi-isomorphism. The Čech nerve
is that of the underlying map of presheaves of sets, whose terms are the fibre powers of `g`. -/
def CechComplexExact (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  ∀ {K' K : Sheaf J (Type u)} (g : K' ⟶ K), Epi g →
    QuasiIso (SimplicialObject.Augmented.freeAbelianSheafEpsNat J
      (Arrow.mk g.hom).augmentedCechNerve F)

/-- The positive-degree half of condition (2): the Čech Hom complex of a surjection of sheaves of
sets is exact in every positive degree. -/
def CechComplexExactPos (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  ∀ {K' K : Sheaf J (Type u)} (g : K' ⟶ K), Epi g → ∀ n : ℕ,
    ((SimplicialObject.Augmented.freeAbelianSheafHomCx J
      (Arrow.mk g.hom).augmentedCechNerve).obj F).ExactAt (n + 1)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] [HasSheafify J AddCommGrpCat.{u}] in
/-- A surjection of sheaves of sets is locally surjective on underlying presheaves. -/
lemma isLocallySurjective_hom_of_epi {K' K : Sheaf J (Type u)}
    (g : K' ⟶ K) (hg : Epi g) : Presheaf.IsLocallySurjective J g.hom :=
  (Sheaf.isLocallySurjective_iff_epi g).2 hg

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] in
/-- Condition (2) implies its positive-degree half. -/
lemma cechComplexExactPos_of_cechComplexExact {F : Sheaf J AddCommGrpCat.{u}}
    (h : CechComplexExact J F) :
    CechComplexExactPos J F := fun {_ _} g hg n ↦
  (quasiIsoAt_iff_exactAt _ (n + 1) (HomologicalComplex.ExactAt.of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ (n + 1) (by omega)))).1
      ((h g hg).quasiIsoAt (n + 1))

/-! #### Surjections from sheaves with vanishing cohomology -/

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- `Ext` out of the free abelian sheaf of a presheaf of sets only depends on its
sheafification. -/
lemma subsingleton_ext_freeAbelianSheaf_of_sheafify (F : Sheaf J AddCommGrpCat.{u})
    (Q : Cᵒᵖ ⥤ Type u) (p : ℕ)
    (h : Subsingleton (Abelian.Ext.{w}
      ((Presheaf.freeAbelianSheaf J).obj ((presheafToSheaf J (Type u)).obj Q).obj) F p)) :
    Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj Q) F p) :=
  have := Presheaf.isIso_freeAbelianSheaf_map_of_W J (toSheafify J Q) (J.W_toSheafify Q)
  subsingleton_ext_of_iso (asIso ((Presheaf.freeAbelianSheaf J).map (toSheafify J Q))) p h

open Stacks.Sites.CoveredByRepresentables in
/-- Assume condition (1) of [Stacks, Tag 07A1]. Then every sheaf of sets `K` admits a surjection
`K' ⟶ K` of sheaves of sets with `H^p(K', F) = 0` for all `p > 0`. -/
theorem exists_epi_subsingleton_ext (F : Sheaf J AddCommGrpCat.{u})
    (h₁ : VanishesOnObjects.{w} J F) (K : Sheaf J (Type u)) :
    ∃ (K' : Sheaf J (Type u)) (g : K' ⟶ K), Epi g ∧
      ∀ p : ℕ, 1 ≤ p →
        Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj K'.obj) F p) := by
  have hE : IsCoveringSubset J (Set.univ : Set C) :=
    fun V ↦ ⟨⊤, J.top_mem V, fun _ _ _ ↦ Set.mem_univ _⟩
  have hpres : PreservesColimitsOfSize.{u, u} (Presheaf.freeAbelianSheaf J) :=
    (Presheaf.freeAbelianSheafAdj J).leftAdjoint_preservesColimits
  have hπ := isLocallySurjective_π J hE K
  have hW := Presheaf.isIso_freeAbelianSheaf_map_of_W J (toSheafify J (P J Set.univ K))
    (J.W_toSheafify (P J Set.univ K))
  refine ⟨F00WS₀ J Set.univ K, π J Set.univ K, Sheaf.epi_of_isLocallySurjective _, fun p hp ↦ ?_⟩
  refine subsingleton_ext_of_iso (asIso ((Presheaf.freeAbelianSheaf J).map
    (toSheafify J (P J Set.univ K)))).symm p ?_
  refine subsingleton_ext_of_iso (PreservesCoproduct.iso (Presheaf.freeAbelianSheaf J)
    (indexFamilyPre J Set.univ K)) p ?_
  have hfac : ∀ i : index J Set.univ K, Subsingleton (Abelian.Ext.{w}
      ((Presheaf.freeAbelianSheaf J).obj (indexFamilyPre J Set.univ K i)) F p) := fun i ↦
    h₁ i.1.val _ ((Functor.RepresentableBy.equivUliftYonedaIso _ i.1.val).symm (Iso.refl _)) p hp
  exact ⟨fun a b ↦ (Abelian.Ext.coproductAddEquiv
    (X := fun i : index J Set.univ K ↦ (Presheaf.freeAbelianSheaf J).obj
      (indexFamilyPre J Set.univ K i)) F p).injective (funext fun i ↦ (hfac i).elim _ _)⟩

/-! #### The dévissage -/

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- The free abelian sheaf complex `s(ℤ_{K'_•}^♯)` of the Čech nerve of `g`, exact in every
positive degree by [Stacks, Tag 01GC]. -/
lemma exactAt_cechNerveFreeChainComplex {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) (i : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk g).cechNerve).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Presheaf.isZero_sheafHomology_cechNerve_of_isLocallySurjective J g hg (i + 1) (by omega)

/-- The opcycles of the free abelian sheaf complex of a Čech nerve form short exact sequences. -/
private lemma shortExact_opcycles_cechNerve (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) (i : ℕ) :
    (ShortComplex.mk
      (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk g).cechNerve).fromOpcycles (i + 1) i)
      (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk g).cechNerve).pOpcycles i)
      (ColimitsOfCohomology.fromOpcycles_comp_pOpcycles _ i)).ShortExact :=
  ColimitsOfCohomology.shortExact_opcycles_of_exactAt _ i
    (exactAt_cechNerveFreeChainComplex J g hg i)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **An injective abelian sheaf satisfies condition (2) of [Stacks, Tag 07A1] in positive
degrees.** For `F` injective and any surjection `g : K' ⟶ K` of sheaves of sets, the Čech Hom
complex `Hom(s(ℤ_{K'_•}^♯), F)` is exact in every positive degree. -/
lemma cechComplexExactPos_of_injective (F : Sheaf J AddCommGrpCat.{u}) [Injective F] :
    CechComplexExactPos J F := fun {_ _} g hg n ↦
  ChainComplex.exactAt_homComplexFunctor_obj _ F (n + 1)
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (exactAt_cechNerveFreeChainComplex J g.hom
        (isLocallySurjective_hom_of_epi J g hg) n))

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **The canonical degree-zero augmentation of the Čech nerve of a locally surjective map
descends to an isomorphism from the degree-zero opcycles onto `ℤ_K^♯`.** -/
@[sga "4 V 1.11" "partial"]
lemma isIso_descOpcycles_cechNerveAugZero {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) :
    IsIso (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk g).augmentedCechNerve.left).descOpcycles
      (SimplicialObject.Augmented.freeAbelianSheafAugZero J (Arrow.mk g).augmentedCechNerve)
      1 (by simp) (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero J
        (Arrow.mk g).augmentedCechNerve 1)) := by
  have hk := Presheaf.cechNerveSheafAugmentation_f_zero_comp_singleObjXSelf_hom J g
  have h : IsIso (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk g).augmentedCechNerve.left).homologyι 0 ≫
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk g).augmentedCechNerve.left).descOpcycles
        (SimplicialObject.Augmented.freeAbelianSheafAugZero J
          (Arrow.mk g).augmentedCechNerve) 1 (by simp)
        (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero J
          (Arrow.mk g).augmentedCechNerve 1)) :=
    Presheaf.isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective J g hg hk 1
      (by simp) (Presheaf.d_comp_cechNerveSheafAugmentation_f_zero J g hk 1)
  exact IsIso.of_isIso_comp_left (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
    (Arrow.mk g).augmentedCechNerve.left).homologyι 0) _

/-- **The degree-zero opcycles of the Čech complex are `ℤ_K^♯`.** -/
def cechOpcyclesZeroIso {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk g).cechNerve).opcycles 0 ≅
      (Presheaf.freeAbelianSheaf J).obj K :=
  @asIso _ _ _ _ _ (isIso_descOpcycles_cechNerveAugZero J g hg)

/-- Assume conditions (1) and (2) of [Stacks, Tag 07A1] and the vanishing of `H^p(Q, F)` for all
presheaves of sets `Q` and all `1 ≤ p ≤ n`. Then `H^{n+1}(Q, F)` vanishes for every presheaf of
sets `Q`. -/
theorem subsingleton_ext_freeAbelianSheaf_succ (F : Sheaf J AddCommGrpCat.{u})
    (h₁ : VanishesOnObjects.{w} J F) (h₂ : CechComplexExactPos J F) (n : ℕ)
    (ih : ∀ (Q : Cᵒᵖ ⥤ Type u) (p : ℕ), 1 ≤ p → p ≤ n →
      Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj Q) F p))
    (Q : Cᵒᵖ ⥤ Type u) :
    Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj Q) F (n + 1)) := by
  refine subsingleton_ext_freeAbelianSheaf_of_sheafify J F Q (n + 1) ?_
  obtain ⟨K', gs, hgs, hK'⟩ := exists_epi_subsingleton_ext J F h₁
    ((presheafToSheaf J (Type u)).obj Q)
  have hg : Presheaf.IsLocallySurjective J gs.hom := isLocallySurjective_hom_of_epi J gs hgs
  set g := gs.hom
  set s := (SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk g).cechNerve
  refine subsingleton_ext_of_iso (cechOpcyclesZeroIso J g hg).symm (n + 1)
    (subsingleton_of_forall_eq 0 fun e ↦ ?_)
  refine ColimitsOfCohomology.ext_eq_zero_of_exact_tower (fun i ↦ s.opcycles i) (fun i ↦ s.X i)
    (fun i ↦ s.fromOpcycles (i + 1) i) (fun i ↦ s.pOpcycles i)
    (fun i ↦ ColimitsOfCohomology.fromOpcycles_comp_pOpcycles s i)
    (shortExact_opcycles_cechNerve J g hg) F n ?_ ?_ e ?_
  · intro i q hi hq hiq c
    exact (ih ((Arrow.mk g).cechNerve.obj (op (SimplexCategory.mk i))) q (by omega)
      (by omega)).elim c 0
  · exact (ChainComplex.exactAt_homComplexFunctor_obj_succ_iff s F n).1 (h₂ gs hgs n)
  · exact (subsingleton_ext_of_iso ((Presheaf.freeAbelianSheaf J).mapIso
      (cechNerveZeroIso g)) (n + 1) (hK' (n + 1) (by omega))).elim _ 0

/-- **The substantive direction of [Stacks, Tag 07A1].** Conditions (1) and (2) imply that `F` is
totally acyclic. Only the positive-degree half of condition (2) is used. -/
theorem isTotallyAcyclic_of_conditions (F : Sheaf J AddCommGrpCat.{u})
    (h₁ : VanishesOnObjects.{w} J F) (h₂ : CechComplexExactPos J F) :
    IsTotallyAcyclic.{w} J F := by
  have key : ∀ (n : ℕ) (Q : Cᵒᵖ ⥤ Type u) (p : ℕ), 1 ≤ p → p ≤ n →
      Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj Q) F p) := by
    intro n
    induction n with
    | zero => intros; omega
    | succ n ih =>
      intro Q p hp hpn
      obtain h | rfl := Nat.lt_or_eq_of_le hpn
      · exact ih Q p hp (by omega)
      · exact subsingleton_ext_freeAbelianSheaf_succ J F h₁ h₂ n ih Q
  exact fun K p hp ↦ key p K.obj p hp le_rfl

/-! #### The converse -/

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **A totally acyclic sheaf has vanishing higher cohomology over every presheaf of sets**, not
only over every sheaf of sets. -/
lemma subsingleton_ext_freeAbelianSheaf_of_isTotallyAcyclic (F : Sheaf J AddCommGrpCat.{u})
    (hF : IsTotallyAcyclic.{w} J F) (Q : Cᵒᵖ ⥤ Type u) (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj Q) F p) :=
  subsingleton_ext_freeAbelianSheaf_of_sheafify J F Q p
    (hF ((presheafToSheaf J (Type u)).obj Q) p hp)

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **A totally acyclic sheaf satisfies condition (1).** -/
lemma vanishesOnObjects_of_isTotallyAcyclic (F : Sheaf J AddCommGrpCat.{u})
    (hF : IsTotallyAcyclic.{w} J F) : VanishesOnObjects.{w} J F :=
  fun _ Q _ p hp ↦ subsingleton_ext_freeAbelianSheaf_of_isTotallyAcyclic J F hF Q p hp

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **`Ext` out of the opcycles of the Čech complex vanishes in positive degrees** for a totally
acyclic sheaf. -/
lemma subsingleton_ext_opcycles_of_isTotallyAcyclic (F : Sheaf J AddCommGrpCat.{u})
    (hF : IsTotallyAcyclic.{w} J F) {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) (i : ℕ) :
    ∀ q : ℕ, 1 ≤ q → Subsingleton (Abelian.Ext.{w}
      (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk g).cechNerve).opcycles i) F q) := by
  induction i with
  | zero =>
    intro q hq
    exact subsingleton_ext_of_iso (cechOpcyclesZeroIso J g hg) q
      (subsingleton_ext_freeAbelianSheaf_of_isTotallyAcyclic J F hF K q hq)
  | succ i ih =>
    intro q hq
    exact subsingleton_ext_X₁_of_shortExact F (shortExact_opcycles_cechNerve J g hg i) q
      (subsingleton_ext_freeAbelianSheaf_of_isTotallyAcyclic J F hF
        ((Arrow.mk g).cechNerve.obj (op (SimplexCategory.mk i))) q hq)
      (ih (q + 1) (by omega))

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **A totally acyclic sheaf satisfies condition (2) in positive degrees.** -/
lemma cechComplexExactPos_of_isTotallyAcyclic (F : Sheaf J AddCommGrpCat.{u})
    (hF : IsTotallyAcyclic.{w} J F) : CechComplexExactPos J F := by
  intro K' K gs hgs n
  have hg : Presheaf.IsLocallySurjective J gs.hom := isLocallySurjective_hom_of_epi J gs hgs
  exact (ChainComplex.exactAt_homComplexFunctor_obj_succ_iff _ F n).2 fun a ↦
    exists_comp_eq_of_subsingleton_extOne F
      (shortExact_opcycles_cechNerve J gs.hom hg n)
      (subsingleton_ext_opcycles_of_isTotallyAcyclic J F hF gs.hom hg n 1 le_rfl) a

/-! #### The degree-zero half of condition (2) -/

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **The canonical degree-zero augmentation of the Čech nerve of a locally surjective map is a
cokernel of the first differential of the free abelian sheaf complex.** -/
def isColimitCokernelCoforkCechNerveAugZero {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) :
    IsColimit (CokernelCofork.ofπ
      (SimplicialObject.Augmented.freeAbelianSheafAugZero J (Arrow.mk g).augmentedCechNerve)
      (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero J
        (Arrow.mk g).augmentedCechNerve 1)) := by
  refine IsColimit.ofIsoColimit
    (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk g).augmentedCechNerve.left).opcyclesIsCokernel (i := 1) (j := 0) (by simp))
    (Cofork.ext (@asIso _ _ _ _ _ (isIso_descOpcycles_cechNerveAugZero J g hg)) ?_)
  exact HomologicalComplex.p_descOpcycles _
    (SimplicialObject.Augmented.freeAbelianSheafAugZero J (Arrow.mk g).augmentedCechNerve) 1
    (by simp) (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero J
      (Arrow.mk g).augmentedCechNerve 1)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **The degree-zero half of condition (2) holds for every abelian sheaf.** Sections over `K`,
restricted along the degree-zero augmentation, are the kernel of the first differential of the
Čech Hom complex. -/
lemma isIso_kernelLift_cechNerveAugZero {K' K : Cᵒᵖ ⥤ Type u} (g : K' ⟶ K)
    (hg : Presheaf.IsLocallySurjective J g) (F : Sheaf J AddCommGrpCat.{u}) :
    IsIso (kernel.lift
      ((preadditiveYoneda.obj F).map
        (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
          (Arrow.mk g).augmentedCechNerve.left).d 1 0).op)
      ((preadditiveYoneda.obj F).map (SimplicialObject.Augmented.freeAbelianSheafAugZero J
        (Arrow.mk g).augmentedCechNerve).op)
      (by rw [← Functor.map_comp, ← op_comp,
        SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero, op_zero,
        Functor.map_zero])) :=
  Limits.isIso_kernelLift_map_op_of_isColimit (preadditiveYoneda.obj F) _ _ _
    (isColimitCokernelCoforkCechNerveAugZero J g hg)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **Condition (2) follows from its positive-degree half.** -/
lemma cechComplexExact_of_cechComplexExactPos {F : Sheaf J AddCommGrpCat.{u}}
    (h : CechComplexExactPos J F) : CechComplexExact J F := by
  intro K' K gs hgs
  refine CochainComplex.quasiIso_mkHomFromSingle_zero _ _ _
    (isIso_kernelLift_cechNerveAugZero J gs.hom
      (isLocallySurjective_hom_of_epi J gs hgs) F) fun q hq ↦ ?_
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact h gs hgs n

/-! #### The criterion -/

/-- Let `𝒞` be a site and `𝓕` an abelian sheaf on it. Then `𝓕` is
totally acyclic ([Stacks, Tag 072Y]) if and only if

1. `H^p(U, 𝓕) = 0` for `p > 0` and every object `U` of `𝒞` — `VanishesOnObjects`; and
2. for every surjection `K' ⟶ K` of sheaves of sets the extended Čech complex
   `0 → H^0(K, 𝓕) → H^0(K', 𝓕) → H^0(K' ×_K K', 𝓕) → …` is exact — `CechComplexExact`. -/
@[stacks 07A1]
theorem isTotallyAcyclic_iff (F : Sheaf J AddCommGrpCat.{u}) :
    IsTotallyAcyclic.{w} J F ↔ (VanishesOnObjects.{w} J F ∧ CechComplexExact J F) :=
  ⟨fun hF ↦ ⟨vanishesOnObjects_of_isTotallyAcyclic J F hF,
      cechComplexExact_of_cechComplexExactPos J
        (cechComplexExactPos_of_isTotallyAcyclic J F hF)⟩,
    fun h ↦ isTotallyAcyclic_of_conditions J F h.1
      (cechComplexExactPos_of_cechComplexExact J h.2)⟩

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] in
/-- **The two forms of condition (2) agree**: exactness of the whole extended Čech complex is
equivalent to its exactness in positive degrees. -/
lemma cechComplexExact_iff_cechComplexExactPos (F : Sheaf J AddCommGrpCat.{u}) :
    CechComplexExact J F ↔ CechComplexExactPos J F :=
  ⟨cechComplexExactPos_of_cechComplexExact J, cechComplexExact_of_cechComplexExactPos J⟩

end

end Stacks.Cohomology

end
