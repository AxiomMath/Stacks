module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.Sections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.ExtTowerVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.TotalAcyclicityOfTheInverseImage
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation

/-! # Cohomology along a full subsite, by descent along representable covers

Let `(C, J)` be a site and let `u : D ⥤ C` be a fully faithful functor, continuous and
cocontinuous for a topology `K` on `D`, so that restriction `g⁻¹` of abelian sheaves along `u`
has a left adjoint `g_!`. Suppose that restriction of an injective abelian sheaf is acyclic over
every object of `D` (Stacks 0D6X over an object).

Call a class `𝔎` of presheaves of sets on `C` *closed under representable covers* when every
member `P` receives a locally surjective map `t : h_{u(d)} ⟶ P` from a representable presheaf of
an object of `D`, all of whose higher tuple presheaves `h_{u(d)} ×_P ⋯ ×_P h_{u(d)}` are again
in `𝔎`. This file proves that for every `P ∈ 𝔎`

* restriction along `u` identifies morphisms `P ⟶ F` into a sheaf of sets with morphisms
  `u^p P ⟶ u^p F`, so that `g_!(ℤ_{u^p P}) ≅ ℤ_P`; and
* `Ext^q(ℤ_{u^p P}, g⁻¹ I) = 0` for every injective abelian sheaf `I` on `C` and every `q ≥ 1`.

For `P` the final presheaf these are the two inputs — the comparison of constant sheaves and the
acyclicity of restricted injectives — from which the comparison of cohomology along `u` follows.

The proof of the second statement is an induction on `q` run along the free abelian Čech
resolution of `ℤ_{u^p P}` attached to `u^p t` (Stacks 01GC): its degree-zero term is the free
abelian sheaf on a representable presheaf, acyclic by hypothesis; its higher terms are the free
abelian sheaves on the restrictions of the tuple presheaves of `t`, which lie in `𝔎` and so are
acyclic in lower degrees by induction; and the extension condition on the top cycles is the
exactness of `Hom(-, g⁻¹ I)` on that resolution, which `g_! ⊣ g⁻¹` and the first statement turn
into exactness of `Hom(-, I)` on the free Čech resolution of `ℤ_P` over `C`, true because `I` is
injective. This is the bookkeeping of the two Čech-to-cohomology spectral sequences of the source
of Stacks 07AK, done by dévissage.

## Main definitions

* `Stacks.Sites.CoverDescent.cechNerveObjIsoTuple`: the degree-`r` term of the Čech nerve of a
  map of presheaves of sets is the presheaf of `(r + 1)`-tuples with a common image.
* `Stacks.Sites.CoverDescent.freeComparison`: the comparison `g_!(ℤ_{u^p M}) ⟶ ℤ_M`.
* `Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers`: the closure condition on `𝔎`.

## Main results

* `Stacks.Sites.CoverDescent.isIso_freeComparison`: the comparison is an isomorphism as soon as
  restriction along `u` is bijective on morphisms out of `M` into sheaves of sets.
* `Stacks.Sites.CoverDescent.restrictHom_bijective_of_mem`: the first statement above.
* `Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem`: the second statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe w' w v u₁ u₂

namespace Stacks.Sites.CoverDescent

variable {C : Type u₁} [Category.{v} C]

/-! ### The Čech nerve as tuples -/

section Nerve

variable {A P : Cᵒᵖ ⥤ Type w} (t : A ⟶ P)

/-- **The degree-`r` term of the Čech nerve of a map of presheaves of sets is the presheaf of
`(r + 1)`-tuples of sections with a common image.** -/
def cechNerveObjIsoTuple (r : ℕ) :
    (Arrow.mk t).cechNerve.obj (op ⦋r⦌) ≅ tuplePresheaf t r where
  hom :=
    { app := fun y => ↾fun x => ⟨fun i =>
          (WidePullback.π (fun _ : Fin (r + 1) => t) i).app y x, fun i => by
        rw [← NatTrans.comp_app_apply, ← NatTrans.comp_app_apply, WidePullback.π_arrow,
          WidePullback.π_arrow]⟩
      naturality := fun y y' g => TypeCat.homEquiv.injective (funext fun x =>
        Subtype.ext (funext fun i => by
          simp only [TypeCat.homEquiv_apply, types_comp_apply, tuplePresheaf_map_val]
          exact NatTrans.naturality_apply (WidePullback.π (fun _ : Fin (r + 1) => t) i) g x)) }
  inv := WidePullback.lift (tupleπ t r 0 ≫ t) (fun i => tupleπ t r i)
    (fun i => natTrans_ext fun y a => a.2 i)
  hom_inv_id := by
    refine WidePullback.hom_ext _ _ _ (fun i => ?_) ?_
    · rw [Category.assoc, WidePullback.lift_π, Category.id_comp]
      exact natTrans_ext fun y x => rfl
    · rw [Category.assoc, WidePullback.lift_base, Category.id_comp, ← Category.assoc,
        ← WidePullback.π_arrow _ 0]
      exact natTrans_ext fun y x => rfl
  inv_hom_id := natTrans_ext fun y a => Subtype.ext (funext fun i => by
    change (WidePullback.π (fun _ : Fin (r + 1) => t) i).app y
      ((WidePullback.lift (tupleπ t r 0 ≫ t) (fun i => tupleπ t r i)
        (fun i => natTrans_ext fun y a => a.2 i)).app y a) = a.1 i
    rw [← NatTrans.comp_app_apply, WidePullback.lift_π]
    rfl)

/-- The tuples of length one are the sections of the source. -/
def tuplePresheafZeroIso : tuplePresheaf t 0 ≅ A where
  hom := tupleπ t 0 0
  inv := { app := fun y => ↾fun a => ⟨fun _ => a, fun _ => rfl⟩ }
  hom_inv_id := natTrans_ext fun y a => Subtype.ext (funext fun i => by
    rw [Fin.fin_one_eq_zero i]; rfl)
  inv_hom_id := natTrans_ext fun y a => rfl

end Nerve

/-! ### The comparison `g_!(ℤ_{u^p M}) ⟶ ℤ_M` -/

section Comparison

variable {D : Type u₂} [Category.{v} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : D ⥤ C) [u.IsContinuous K J]
  [HasSheafify J AddCommGrpCat.{max v w}] [HasSheafify K AddCommGrpCat.{max v w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).IsRightAdjoint]

/-- The restriction along `u` of the unit `M ⟶ ℤ_M` of the free-abelian-sheaf adjunction, read
as a morphism into the underlying presheaf of sets of `g⁻¹ ℤ_M`. -/
def unitRestrict (M : Cᵒᵖ ⥤ Type (max v w)) :
    u.op ⋙ M ⟶ (sheafToPresheaf K AddCommGrpCat.{max v w} ⋙ Presheaf.forgetAbelian).obj
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj
        ((Presheaf.freeAbelianSheaf.{max v w} J).obj M)) :=
  Functor.whiskerLeft u.op ((Presheaf.freeAbelianSheafAdj.{max v w} J).unit.app M)

/-- **The comparison `g_!(ℤ_{u^p M}) ⟶ ℤ_M`.** It is adjoint, under `g_! ⊣ g⁻¹` and the
free-abelian-sheaf adjunction on `D`, to the restriction along `u` of the unit
`M ⟶ ℤ_M` of the free-abelian-sheaf adjunction on `C`. -/
def freeComparison (M : Cᵒᵖ ⥤ Type (max v w)) :
    (u.sheafPullback AddCommGrpCat.{max v w} K J).obj
        ((Presheaf.freeAbelianSheaf.{max v w} K).obj (u.op ⋙ M)) ⟶
      (Presheaf.freeAbelianSheaf.{max v w} J).obj M :=
  ((u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).homEquiv _ _).symm
    (((Presheaf.freeAbelianSheafAdj.{max v w} K).homEquiv _ _).symm (unitRestrict J K u M))

/-- **Morphisms out of `ℤ_M`, precomposed with the comparison, are the restrictions of the
corresponding morphisms of presheaves of sets.** Under the two adjunctions, precomposing a
morphism `ℤ_M ⟶ F` with `freeComparison` is restricting the morphism `M ⟶ F` it is adjoint to. -/
lemma homEquiv_homEquiv_freeComparison_comp (M : Cᵒᵖ ⥤ Type (max v w))
    (F : Sheaf J AddCommGrpCat.{max v w}) (x : (Presheaf.freeAbelianSheaf.{max v w} J).obj M ⟶ F) :
    (Presheaf.freeAbelianSheafAdj.{max v w} K).homEquiv _ _
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).homEquiv _ _
          (freeComparison J K u M ≫ x)) =
      restrictHom u M _ ((Presheaf.freeAbelianSheafAdj.{max v w} J).homEquiv _ _ x) := by
  rw [Adjunction.homEquiv_naturality_right, freeComparison, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  rfl

/-- **The comparison is natural in the presheaf.** -/
lemma freeComparison_naturality {M M' : Cᵒᵖ ⥤ Type (max v w)} (m : M ⟶ M') :
    (u.sheafPullback AddCommGrpCat.{max v w} K J).map
        ((Presheaf.freeAbelianSheaf.{max v w} K).map (Functor.whiskerLeft u.op m)) ≫
      freeComparison J K u M' =
      freeComparison J K u M ≫ (Presheaf.freeAbelianSheaf.{max v w} J).map m := by
  apply ((u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).homEquiv _ _).injective
  apply ((Presheaf.freeAbelianSheafAdj.{max v w} K).homEquiv _ _).injective
  rw [homEquiv_homEquiv_freeComparison_comp, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_left, freeComparison, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact congrArg (Functor.whiskerLeft u.op)
    ((Presheaf.freeAbelianSheafAdj.{max v w} J).unit.naturality m)

/-- The comparison, as a natural transformation of functors of the presheaf. -/
@[simps]
def freeComparisonNatTrans :
    (Functor.whiskeringLeft _ _ (Type (max v w))).obj u.op ⋙
        Presheaf.freeAbelianSheaf.{max v w} K ⋙ u.sheafPullback AddCommGrpCat.{max v w} K J ⟶
      Presheaf.freeAbelianSheaf.{max v w} J where
  app M := freeComparison J K u M
  naturality _ _ m := freeComparison_naturality J K u m

/-- **The comparison `g_!(ℤ_{u^p M}) ⟶ ℤ_M` is an isomorphism as soon as restriction along `u`
is bijective on morphisms out of `M` into sheaves of sets.** By the Yoneda lemma it suffices
that precomposition with it be bijective on morphisms into every abelian sheaf `F`; under the two
adjunctions that precomposition is restriction along `u` of morphisms `M ⟶ F` of presheaves of
sets, `F` being a sheaf of sets. -/
lemma isIso_freeComparison (M : Cᵒᵖ ⥤ Type (max v w))
    (h : ∀ F : Cᵒᵖ ⥤ Type (max v w), Presieve.IsSheaf J F →
      Function.Bijective (restrictHom u M F)) :
    IsIso (freeComparison J K u M) := by
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have hT : Presieve.IsSheaf J
      ((sheafToPresheaf J AddCommGrpCat.{max v w} ⋙ Presheaf.forgetAbelian).obj T) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget AddCommGrpCat.{max v w})).obj T).property
  have key : (fun x : (Presheaf.freeAbelianSheaf.{max v w} J).obj M ⟶ T =>
        freeComparison J K u M ≫ x) =
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).homEquiv _ _).symm ∘
        ((Presheaf.freeAbelianSheafAdj.{max v w} K).homEquiv _ _).symm ∘
          restrictHom u M _ ∘ (Presheaf.freeAbelianSheafAdj.{max v w} J).homEquiv _ _ := by
    funext x
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, homEquiv_homEquiv_freeComparison_comp]
    rfl
  rw [key]
  exact ((u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).homEquiv _ _).symm.bijective.comp
    (((Presheaf.freeAbelianSheafAdj.{max v w} K).homEquiv _ _).symm.bijective.comp
      ((h _ hT).comp ((Presheaf.freeAbelianSheafAdj.{max v w} J).homEquiv _ _).bijective))

/-- The comparison `g_!(ℤ_{u^p M}) ⟶ ℤ_M` at the terms of the Čech nerve of `t`, as an
isomorphism of simplicial abelian sheaves, when it is an isomorphism termwise. -/
def freeComparisonCechNerveIso {A P : Cᵒᵖ ⥤ Type (max v w)} (t : A ⟶ P)
    [∀ n : SimplexCategoryᵒᵖ, IsIso (freeComparison J K u ((Arrow.mk t).cechNerve.obj n))] :
    (Arrow.mk t).cechNerve ⋙ ((Functor.whiskeringLeft _ _ (Type (max v w))).obj u.op ⋙
        Presheaf.freeAbelianSheaf.{max v w} K ⋙ u.sheafPullback AddCommGrpCat.{max v w} K J) ≅
      (Arrow.mk t).cechNerve ⋙ Presheaf.freeAbelianSheaf.{max v w} J :=
  NatIso.ofComponents (fun n => asIso (freeComparison J K u ((Arrow.mk t).cechNerve.obj n)))
    (fun g => freeComparison_naturality J K u ((Arrow.mk t).cechNerve.map g))

/-- **The free abelian Čech resolution along a representable cover, pushed forward by `g_!`.**
If the comparison `g_!(ℤ_{u^p M}) ⟶ ℤ_M` is an isomorphism at every term `M` of the Čech nerve of
`t : A ⟶ P`, then `g_!` carries the free abelian sheaf complex of the Čech nerve of `u^p t` to that
of `t`. -/
def freeCechComparisonIso {A P : Cᵒᵖ ⥤ Type (max v w)} (t : A ⟶ P)
    [∀ n : SimplexCategoryᵒᵖ, IsIso (freeComparison J K u ((Arrow.mk t).cechNerve.obj n))] :
    ((u.sheafPullback AddCommGrpCat.{max v w} K J).mapHomologicalComplex _).obj
        ((SimplicialObject.freeAbelianSheafComplexFunctor.{max v w} K).obj
          (Arrow.mk (Functor.whiskerLeft u.op t)).cechNerve) ≅
      (SimplicialObject.freeAbelianSheafComplexFunctor.{max v w} J).obj (Arrow.mk t).cechNerve :=
  have : (u.sheafPullback AddCommGrpCat.{max v w} K J).Additive :=
    (u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).left_adjoint_additive
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (u.sheafPullback AddCommGrpCat.{max v w} K J)).app
      ((Arrow.mk (Functor.whiskerLeft u.op t)).cechNerve ⋙
        Presheaf.freeAbelianSheaf.{max v w} K) ≪≫
    (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max v w})).mapIso
      (Functor.isoWhiskerRight (Functor.isoWhiskerRight
          (Arrow.cechNerveComp ((Functor.whiskeringLeft _ _ (Type (max v w))).obj u.op)
            (Arrow.mk t)).symm
          (Presheaf.freeAbelianSheaf.{max v w} K)) (u.sheafPullback AddCommGrpCat.{max v w} K J) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.associator _ _ _ ≪≫
        freeComparisonCechNerveIso J K u t)

end Comparison

/-! ### The free Čech resolution in degree zero -/

section DegreeZero

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}] {A P : Cᵒᵖ ⥤ Type w}
  (t : A ⟶ P)

/-- **Stacks 01GC in degree zero, on opcycles.** For a locally surjective map of presheaves of
sets, the degree-zero augmentation of the free abelian sheaf complex of its Čech nerve descends to
an isomorphism from the degree-zero opcycles onto the free abelian sheaf on the target. -/
lemma isIso_descOpcycles_freeAbelianSheafAugZero (ht : Presheaf.IsLocallySurjective J t) :
    IsIso (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
        (Arrow.mk t).augmentedCechNerve.left).descOpcycles
      (SimplicialObject.Augmented.freeAbelianSheafAugZero J (Arrow.mk t).augmentedCechNerve)
      1 (by simp) (SimplicialObject.Augmented.d_comp_freeAbelianSheafAugZero J
        (Arrow.mk t).augmentedCechNerve 1)) := by
  have hk := Presheaf.cechNerveSheafAugmentation_f_zero_comp_singleObjXSelf_hom J t
  have := Presheaf.isIso_homologyι_descOpcycles_cechNerve_of_isLocallySurjective J t ht hk 1
    (by simp) (Presheaf.d_comp_cechNerveSheafAugmentation_f_zero J t hk 1)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    (((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk t).augmentedCechNerve.left).homologyι 0) _ inferInstance this

/-- The degree-zero opcycles of the free abelian sheaf complex of the Čech nerve of a locally
surjective map are the free abelian sheaf on its target. -/
def cechOpcyclesZeroIso (ht : Presheaf.IsLocallySurjective J t) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk t).cechNerve).opcycles 0 ≅
      (Presheaf.freeAbelianSheaf J).obj P :=
  @asIso _ _ _ _ _ (isIso_descOpcycles_freeAbelianSheafAugZero J t ht)

/-- **Stacks 01GC in positive degrees**, read as exactness. -/
lemma exactAt_freeAbelianSheafComplex_cechNerve (ht : Presheaf.IsLocallySurjective J t)
    (i : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj
      (Arrow.mk t).cechNerve).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Presheaf.isZero_sheafHomology_cechNerve_of_isLocallySurjective J t ht (i + 1) (by omega)

end DegreeZero

/-! ### Descent along representable covers -/

section Main

variable {D : Type u₂} [Category.{v} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : D ⥤ C) [u.IsContinuous K J] [u.Full] [u.Faithful]

/-- **A class of presheaves of sets closed under representable covers.** Every member `P`
receives a map `t : h_{u(d)} ⟶ P` from the representable presheaf of an object of `D` which is
locally surjective, and remains so after restriction to `D`, each of whose tuple presheaves
`h_{u(d)} ×_P ⋯ ×_P h_{u(d)}` of length at least two is isomorphic to a member.

Local surjectivity after restriction is automatic when `u` is cocontinuous
(`CategoryTheory.Presheaf.isLocallySurjective_whisker`); it is stated separately so that no
cocontinuity instance is needed alongside the left adjoint of restriction. -/
def IsClosedUnderRepresentableCovers (𝔎 : (Cᵒᵖ ⥤ Type (max v w)) → Prop) : Prop :=
  ∀ P, 𝔎 P → ∃ (d : D) (t : uliftYoneda.{w}.obj (u.obj d) ⟶ P),
    Presheaf.IsLocallySurjective J t ∧ Presheaf.IsLocallySurjective K (Functor.whiskerLeft u.op t) ∧
      ∀ r : ℕ, ∃ Q, 𝔎 Q ∧ Nonempty (tuplePresheaf t (r + 1) ≅ Q)

variable {J u} {𝔎 : (Cᵒᵖ ⥤ Type (max v w)) → Prop}

omit [u.Faithful] in
include K in
/-- **Degree zero.** Restriction along `u` is bijective on morphisms out of a member of a class
closed under representable covers into a sheaf of sets. -/
theorem restrictHom_bijective_of_mem (h𝔎 : IsClosedUnderRepresentableCovers J K u 𝔎)
    {P : Cᵒᵖ ⥤ Type (max v w)} (hP : 𝔎 P) (F : Cᵒᵖ ⥤ Type (max v w))
    (hF : Presieve.IsSheaf J F) : Function.Bijective (restrictHom u P F) := by
  obtain ⟨d, t, ht, htK, htup⟩ := h𝔎 P hP
  have := ht
  have := htK
  refine restrictHom_bijective_of_isLocallySurjective u J K t F hF
    (restrictHom_bijective_uliftYoneda u d F) ?_
  obtain ⟨Q, hQ, ⟨e⟩⟩ := htup 0
  obtain ⟨d', t', ht', -, -⟩ := h𝔎 Q hQ
  have := ht'
  exact restrictHom_injective_of_iso u e F
    (restrictHom_injective_of_isLocallySurjective u J t' F hF
      (restrictHom_bijective_uliftYoneda u d' F).1)

omit [u.Faithful] in
include K in
/-- Restriction along `u` is bijective on morphisms out of every term of the Čech nerve of a
representable cover of a member of the class. -/
lemma restrictHom_bijective_cechNerve (h𝔎 : IsClosedUnderRepresentableCovers J K u 𝔎)
    {P : Cᵒᵖ ⥤ Type (max v w)} {d : D} (t : uliftYoneda.{w}.obj (u.obj d) ⟶ P)
    (htup : ∀ r : ℕ, ∃ Q, 𝔎 Q ∧ Nonempty (tuplePresheaf t (r + 1) ≅ Q))
    (n : SimplexCategoryᵒᵖ) (F : Cᵒᵖ ⥤ Type (max v w)) (hF : Presieve.IsSheaf J F) :
    Function.Bijective (restrictHom u ((Arrow.mk t).cechNerve.obj n) F) := by
  refine restrictHom_bijective_of_iso u (cechNerveObjIsoTuple t n.unop.len) F ?_
  rcases h : n.unop.len with _ | r
  · exact restrictHom_bijective_of_iso u (tuplePresheafZeroIso t) F
      (restrictHom_bijective_uliftYoneda u d F)
  · obtain ⟨Q, hQ, ⟨e⟩⟩ := htup r
    exact restrictHom_bijective_of_iso u e F (restrictHom_bijective_of_mem K h𝔎 hQ F hF)

end Main

/-! ### Acyclicity -/

section Ext

open Stacks.Cohomology.ColimitsOfCohomology

variable {D : Type u₁} [Category.{v} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {u : D ⥤ C}

/-- For a fully faithful `u`, the restriction of the representable presheaf of `u(d)` is the
representable presheaf of `d`. -/
def uliftYonedaRestrictIso [u.Full] [u.Faithful] (d : D) :
    u.op ⋙ uliftYoneda.{w}.obj (u.obj d) ≅ uliftYoneda.{w}.obj d :=
  NatIso.ofComponents (fun y => Equiv.toIso (Equiv.ulift.trans
      (((Functor.FullyFaithful.ofFullyFaithful u).homEquiv).symm.trans Equiv.ulift.symm)))
    (fun {y y'} g => TypeCat.homEquiv.injective (funext fun a => by
      simp only [TypeCat.homEquiv_apply, types_comp_apply]
      change ULift.up (u.preimage (u.map g.unop ≫ a.down)) =
        ULift.up (g.unop ≫ u.preimage a.down)
      rw [Functor.preimage_comp, Functor.preimage_map]))

variable [u.IsContinuous K J] [u.Full] [u.Faithful]
  [HasSheafify J AddCommGrpCat.{max v w}] [HasSheafify K AddCommGrpCat.{max v w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).IsRightAdjoint]
  [HasExt.{w'} (Sheaf K AddCommGrpCat.{max v w})]
  {𝔎 : (Cᵒᵖ ⥤ Type (max v w)) → Prop}

/-- **The inductive step.** Suppose restriction of injective abelian sheaves is acyclic over the
objects of `D`, and that `Ext^{m+1}(ℤ_{u^p Q}, g⁻¹ I)` vanishes for every member `Q` of a class
closed under representable covers, every injective `I` and every `m < n`. Then
`Ext^{n+1}(ℤ_{u^p P}, g⁻¹ I) = 0` for every member `P`.

Choose a representable cover `t` of `P` and run the dévissage `ext_eq_zero_of_exact_tower` along
the opcycles of the free abelian Čech resolution of `ℤ_{u^p P}` attached to `u^p t`. Its
degree-zero term is the free abelian sheaf on a representable presheaf of `D`, which kills the
restriction of the class to it; its higher terms are free abelian sheaves on restrictions of
members of the class, acyclic in the degrees the dévissage meets by the inductive hypothesis; and
the extension condition on its top opcycles is exactness of the complex `Hom(-, g⁻¹ I)` on it,
which `g_! ⊣ g⁻¹` and `Stacks.Sites.CoverDescent.freeCechComparisonIso` identify with exactness
of `Hom(-, I)` on the free abelian Čech resolution of `ℤ_P` over `C`, true because `I` is
injective. -/
theorem ext_restriction_eq_zero_step (h𝔎 : IsClosedUnderRepresentableCovers J K u 𝔎)
    (hobj : ∀ (I : Sheaf J AddCommGrpCat.{max v w}) [Injective I] (d : D) (n : ℕ)
      (a : Abelian.Ext.{w'} (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{w} K d)
        ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj I) (n + 1)), a = 0)
    (n : ℕ)
    (ih : ∀ (Q : Cᵒᵖ ⥤ Type (max v w)), 𝔎 Q → ∀ (I : Sheaf J AddCommGrpCat.{max v w}),
      Injective I → ∀ m < n, ∀ a : Abelian.Ext.{w'} ((Presheaf.freeAbelianSheaf K).obj (u.op ⋙ Q))
        ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj I) (m + 1), a = 0)
    {P : Cᵒᵖ ⥤ Type (max v w)} (hP : 𝔎 P) (I : Sheaf J AddCommGrpCat.{max v w}) [Injective I]
    (a : Abelian.Ext.{w'} ((Presheaf.freeAbelianSheaf K).obj (u.op ⋙ P))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj I) (n + 1)) : a = 0 := by
  obtain ⟨d, t, ht, ht', htup⟩ := h𝔎 P hP
  have := ht
  have := ht'
  let G := (u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj I
  let s := (SimplicialObject.freeAbelianSheafComplexFunctor.{max v w} K).obj
    (Arrow.mk (Functor.whiskerLeft u.op t)).cechNerve
  have hst : ∀ i : ℕ, (ShortComplex.mk (s.fromOpcycles (i + 1) i) (s.pOpcycles i)
      (fromOpcycles_comp_pOpcycles s i)).ShortExact := fun i =>
    shortExact_opcycles_of_exactAt s i
      (exactAt_freeAbelianSheafComplex_cechNerve K (Functor.whiskerLeft u.op t) ht' i)
  let E := cechOpcyclesZeroIso K (Functor.whiskerLeft u.op t) ht'
  -- the degree-zero term is the free abelian sheaf on a representable presheaf of `D`
  have h0 : ∀ b : Abelian.Ext.{w'} (s.X 0) G (n + 1), b = 0 := fun b =>
    ext_eq_zero_of_iso_first ((Presheaf.freeAbelianSheaf.{max v w} K).mapIso
      (cechNerveObjIsoTuple (Functor.whiskerLeft u.op t) 0 ≪≫
        tuplePresheafZeroIso (Functor.whiskerLeft u.op t) ≪≫ uliftYonedaRestrictIso d))
      (n + 1) (hobj I d n) b
  -- the higher terms are the free abelian sheaves on restrictions of members of the class
  have hv : ∀ (i q : ℕ), 0 < i → 0 < q → i + q = n + 1 →
      ∀ b : Abelian.Ext.{w'} (s.X i) G q, b = 0 := by
    intro i q hi hq hiq b
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    obtain ⟨Q, hQ, ⟨e⟩⟩ := htup i'
    exact ext_eq_zero_of_iso_first ((Presheaf.freeAbelianSheaf.{max v w} K).mapIso
      (cechNerveObjIsoTuple (Functor.whiskerLeft u.op t) (i' + 1) ≪≫
        Functor.isoWhiskerLeft u.op e)) (q' + 1) (ih Q hQ I inferInstance q' (by omega)) b
  -- the extension condition, from the injectivity of `I` over `C`
  have hiso : ∀ m : SimplexCategoryᵒᵖ,
      IsIso (freeComparison J K u ((Arrow.mk t).cechNerve.obj m)) := fun m =>
    isIso_freeComparison J K u _ fun F hF => restrictHom_bijective_cechNerve K h𝔎 t htup m F hF
  have hext : ∀ c : s.opcycles (n + 1) ⟶ G, ∃ b : s.X n ⟶ G,
      s.fromOpcycles (n + 1) n ≫ b = c := by
    let sC := (SimplicialObject.freeAbelianSheafComplexFunctor.{max v w} J).obj
      (Arrow.mk t).cechNerve
    have hmono : Mono (sC.fromOpcycles (n + 1) n) :=
      (shortExact_opcycles_of_exactAt sC n
        (exactAt_freeAbelianSheafComplex_cechNerve J t ht n)).mono_f
    have hC : ((ChainComplex.homComplexFunctor sC).obj I).ExactAt (n + 1) :=
      (ChainComplex.exactAt_homComplexFunctor_obj_succ_iff sC I n).2 fun c =>
        ⟨Injective.factorThru c (sC.fromOpcycles (n + 1) n), Injective.comp_factorThru _ _⟩
    have : (u.sheafPullback AddCommGrpCat.{max v w} K J).Additive :=
      (u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J).left_adjoint_additive
    have hD : ((ChainComplex.homComplexFunctor s).obj G).ExactAt (n + 1) :=
      hC.of_iso (ChainComplex.homComplexFunctorMapIso (freeCechComparisonIso J K u t) I ≪≫
        (ChainComplex.homComplexFunctorAdjunctionIso
          (u.sheafAdjunctionContinuous AddCommGrpCat.{max v w} K J) s I).symm)
    exact (ChainComplex.exactAt_homComplexFunctor_obj_succ_iff s G n).1 hD
  have hX : (Abelian.Ext.mk₀ E.hom).comp a (zero_add _) = 0 :=
    ext_eq_zero_of_exact_tower (fun i => s.opcycles i) (fun i => s.X i)
      (fun i => s.fromOpcycles (i + 1) i) (fun i => s.pOpcycles i)
      (fromOpcycles_comp_pOpcycles s) hst G n hv hext _ (by
        rw [Abelian.Ext.mk₀_comp_mk₀_assoc]
        exact h0 _)
  have hh := congrArg (fun b => (Abelian.Ext.mk₀ E.inv).comp b (zero_add _)) hX
  simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, E.inv_hom_id, Abelian.Ext.mk₀_id_comp,
    Abelian.Ext.comp_zero] using hh

/-- **Acyclicity of restricted injectives over the members of a class closed under
representable covers.** If restriction of an injective abelian sheaf along `u` is acyclic over
every object of `D`, then for every member `P` of a class closed under representable covers and
every injective abelian sheaf `I` on `C`,

`Ext^q(ℤ_{u^p P}, g⁻¹ I) = 0` for `q ≥ 1`. -/
theorem ext_restriction_eq_zero_of_mem (h𝔎 : IsClosedUnderRepresentableCovers J K u 𝔎)
    (hobj : ∀ (I : Sheaf J AddCommGrpCat.{max v w}) [Injective I] (d : D) (n : ℕ)
      (a : Abelian.Ext.{w'} (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{w} K d)
        ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj I) (n + 1)), a = 0)
    {P : Cᵒᵖ ⥤ Type (max v w)} (hP : 𝔎 P) (I : Sheaf J AddCommGrpCat.{max v w}) [Injective I]
    (n : ℕ) (a : Abelian.Ext.{w'} ((Presheaf.freeAbelianSheaf K).obj (u.op ⋙ P))
      ((u.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).obj I) (n + 1)) : a = 0 := by
  induction n using Nat.strong_induction_on generalizing P I with
  | _ n ih =>
    exact ext_restriction_eq_zero_step h𝔎 hobj n
      (fun Q hQ I' hI' m hm b => @ih m hm Q hQ I' hI' b) hP I a

end Ext

/-! ### The free abelian sheaf on a presheaf with one-point values -/

section Unique

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- **The free abelian sheaf on a presheaf of sets all of whose values are one-point sets is the
constant sheaf `ℤ`**: sectionwise, the free abelian group on a point is `ℤ`. -/
def freeAbelianSheafIsoConstantSheafOfUnique (Q : Cᵒᵖ ⥤ Type w) (hQ : ∀ y, Unique (Q.obj y)) :
    (Presheaf.freeAbelianSheaf J).obj Q ≅
      (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{w}).mapIso (NatIso.ofComponents
    (fun y => letI := hQ y
      ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {y y'} f => by
      let := hQ y
      let := hQ y'
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro t
      change AddEquiv.ulift.symm ((FreeAbelianGroup.uniqueEquiv _)
          (FreeAbelianGroup.map (Q.map f) (FreeAbelianGroup.of t))) =
        AddEquiv.ulift.symm ((FreeAbelianGroup.uniqueEquiv _) (FreeAbelianGroup.of t))
      simp [FreeAbelianGroup.uniqueEquiv]))

end Unique

end Stacks.Sites.CoverDescent

end
