module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison

/-!
# Right derived functors and direct sums of bounded below objects

Let `F : A ⥤ C` be a left exact additive functor out of a Grothendieck abelian category, with
unbounded right derived functor `RF : D(A) ⥤ D(C)`, and suppose that every ordinary right derived
functor `R^q F` commutes with direct sums. Then:

* `RF` commutes with direct sums of objects of `D(A)` which are *uniformly* bounded below
  (`Stacks.DerivedFunctor.Coproducts.preservesColimit_of_forall_isGE`): such a family has
  representatives by complexes of injectives vanishing in degrees `< a`, whose direct sum is a
  bounded below complex of `F`-acyclic objects, and on such complexes `RF` is computed termwise.
* If `𝒫 ⊆ D(A)` is a full subcategory closed under shifts and truncations and under direct sums,
  and `RF` has a uniform bound on `𝒫` — `H^n(RF(E)) = 0` for `n ≥ N` whenever `E ∈ 𝒫` lies in
  `D^{≤ 0}` — then `RF` restricted to `𝒫` commutes with direct sums
  (`Stacks.DerivedFunctor.Coproducts.preservesColimitsOfShape_ι_comp_of_uniform_bound`).
  Indeed `H^n(RF(E)) = H^n(RF(τ_{≥ n - N + 1} E))` for `E ∈ 𝒫`, and the truncation functors
  commute with direct sums.

This is the homological algebra in the proof of [Stacks, Tag 08FB]: the derived direct image
along a quasi-compact quasi-separated morphism of algebraic spaces commutes with direct sums of
complexes with quasi-coherent cohomology, the bound being the finite cohomological dimension of
[Stacks, Tag 08FA] on quasi-coherent modules.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe i

namespace Stacks.DerivedFunctor.Coproducts

section BoundedBelow

variable {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory C]

/-- A colimit cocone is carried to a colimit cocone by `H` when it is by `G` and a natural
transformation `G ⟶ H` is invertible on the diagram and on the apex. -/
private noncomputable def isColimitMapCoconeOfIsIsoApp
    {X D J : Type*} [Category* X] [Category* D] [Category* J]
    (K : J ⥤ X) (c : Cocone K) (G H : X ⥤ D) (β : G ⟶ H)
    (hlegs : ∀ j : J, IsIso (β.app (K.obj j))) (hapex : IsIso (β.app c.pt))
    (hG : IsColimit (G.mapCocone c)) : IsColimit (H.mapCocone c) := by
  have : IsIso (Functor.whiskerLeft K β) :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun j => hlegs j)
  let e : K ⋙ G ≅ K ⋙ H := asIso (Functor.whiskerLeft K β)
  have h : IsColimit ((Cocone.precompose e.inv).obj (G.mapCocone c)) :=
    (IsColimit.precomposeHomEquiv e.symm (G.mapCocone c)).symm hG
  refine IsColimit.ofIsoColimit h (Cocone.ext (asIso (β.app c.pt)) ?_)
  intro j
  simp [e]

/-- The comparison `Q ∘ F ⟶ RF ∘ Q` on cochain complexes induced by the unit `α` of a right
derived functor. -/
private noncomputable def complexUnit (F : A ⥤ C) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) α ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF).hom

private lemma isZero_obj_sigma {X D : Type*} [Category* X] [Category* D] [HasZeroMorphisms D]
    (G : X ⥤ D) {I : Type*} (K : I → X) [HasCoproduct K]
    [PreservesColimit (Discrete.functor K) G] (hK : ∀ i, IsZero (G.obj (K i))) :
    IsZero (G.obj (∐ K)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (isColimitOfPreserves G (coproductIsCoproduct K)).hom_ext
  rintro ⟨i⟩
  exact (hK i).eq_of_src _ _

/-- A direct sum of `F`-acyclic objects is `F`-acyclic when the `R^q F` commute with direct
sums. -/
private lemma rightAcyclic_sigma_X [EnoughInjectives A]
    (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F]
    (I : Type i) [HasColimitsOfShape (Discrete I) A]
    (hcoproducts : ∀ q : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived q))
    (K : I → CochainComplex A ℤ) (hK : ∀ j n, F.rightAcyclic ((K j).X n)) (n : ℤ) :
    F.rightAcyclic ((∐ K).X n) := by
  apply (rightAcyclic_iff_isZero_rightDerived F _).2
  intro q hq
  have := hcoproducts q
  exact isZero_obj_sigma (HomologicalComplex.eval A (ComplexShape.up ℤ) n ⋙ F.rightDerived q)
    K (fun j => (rightAcyclic_iff_isZero_rightDerived F _).1 (hK j n) q hq)

omit [HasDerivedCategory A] in
private lemma sigma_isStrictlyGE {I : Type i} [HasCoproductsOfShape I A]
    (K : I → CochainComplex A ℤ) (a : ℤ) (hK : ∀ j, (K j).IsStrictlyGE a) :
    (∐ K).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact isZero_obj_sigma (HomologicalComplex.eval A (ComplexShape.up ℤ) n) K
    (fun j => (CochainComplex.isStrictlyGE_iff (K j) a).1 (hK j) n hn)

/-- **The right derived functor commutes with direct sums of uniformly bounded below objects.**
If `F` is left exact, `A` is Grothendieck abelian and every `R^q F` commutes with direct sums
indexed by `I`, then `RF` commutes with the direct sum of any family of objects of `D(A)` all
lying in `D^{≥ a}` for one `a`. -/
theorem preservesColimit_of_forall_isGE
    [IsGrothendieckAbelian.{i} A] (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F]
    (I : Type i) [HasCoproductsOfShape I C]
    [PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A))]
    [PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := C))]
    (hcoproducts : ∀ q : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived q))
    (RF : DerivedCategory A ⥤ DerivedCategory C)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (E : I → DerivedCategory A) (a : ℤ) (hE : ∀ j, (E j).IsGE a) :
    PreservesColimit (Discrete.functor E) RF := by
  classical
  have hrep (j : I) : ∃ K : CochainComplex A ℤ, K.IsStrictlyGE a ∧
      (∀ n, Injective (K.X n)) ∧ Nonempty (E j ≅ DerivedCategory.Q.obj K) := by
    have := hE j
    obtain ⟨L, hL, ⟨e⟩⟩ := (E j).exists_iso_Q_obj_of_isGE a
    let P : ObjectProperty A := fun X => Injective X
    have : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
    obtain ⟨K, f, hf, hK, _, hge⟩ :=
      CochainComplex.exists_quasiIso_prop_isStrictlyGE P
        (fun X => ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) a L
    exact ⟨K, hge, hK, ⟨e ≪≫ asIso (DerivedCategory.Q.map f)⟩⟩
  choose K hK hinj he using hrep
  have hacyclic (j : I) (n : ℤ) : F.rightAcyclic ((K j).X n) := by
    apply (rightAcyclic_iff_isZero_rightDerived F _).2
    intro q hq
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have : Injective ((K j).X n) := hinj j n
    exact F.isZero_rightDerived_obj_injective_succ q _
  have := hcoproducts 0
  have : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let β := complexUnit F RF α
  have hβ (L : CochainComplex A ℤ) (b : ℤ) (hL : L.IsStrictlyGE b)
      (hLa : ∀ n, F.rightAcyclic (L.X n)) : IsIso (β.app L) := by
    have := Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic F RF α L ⟨b, hL⟩ hLa
    dsimp [β, complexUnit]
    infer_instance
  have hQ : PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A) ⋙ RF) := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    exact isColimitMapCoconeOfIsIsoApp (Discrete.functor K) (Cofan.mk (∐ K) (Sigma.ι K)) G _ β
      (fun j => hβ _ a (hK j.as) (hacyclic j.as))
      (hβ _ a (sigma_isStrictlyGE K a hK) (rightAcyclic_sigma_X F I hcoproducts K hacyclic))
      (isColimitOfPreserves G (coproductIsCoproduct K))
  have : PreservesColimit (Discrete.functor K ⋙ DerivedCategory.Q) RF :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (DerivedCategory.Q (C := A)) (coproductIsCoproduct K))
      (isColimitOfPreserves (DerivedCategory.Q (C := A) ⋙ RF) (coproductIsCoproduct K))
  exact preservesColimit_of_iso_diagram (K₁ := Discrete.functor K ⋙ DerivedCategory.Q) RF
    (Discrete.natIso fun j => ((he j.as).some).symm)

private lemma preservesColimitsOfShape_of_jointlyReflects
    {C D : Type*} [Category* C] [Category* D]
    {J A : Type*} [Category* J] {E : A → Type*} [∀ a, Category (E a)]
    (F : C ⥤ D) (H : ∀ a, D ⥤ E a) (hH : JointlyReflectIsomorphisms H)
    [HasColimitsOfShape J D]
    [∀ a, PreservesColimitsOfShape J (H a)]
    [∀ a, PreservesColimitsOfShape J (F ⋙ H a)] :
    PreservesColimitsOfShape J F := by
  refine ⟨fun {K} => ⟨fun {c} hc => ⟨?_⟩⟩⟩
  exact hH.jointlyReflectsColimit fun a => isColimitOfPreserves (F ⋙ H a) hc

private lemma isIso_homology_map_truncGE_of_isZero
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    (R : DerivedCategory A ⥤ DerivedCategory C)
    [R.CommShift ℤ] [R.IsTriangulated]
    (E : DerivedCategory A) (a n : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor C n).obj
      (R.obj ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E))))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C (n + 1)).obj
      (R.obj ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)))) :
    IsIso ((DerivedCategory.homologyFunctor C n).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ a).app E))) := by
  let T := R.mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory C) := R.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) E)
  have : Mono ((DerivedCategory.homologyFunctor C n).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff
      T hT n).2 (h₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor C n).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff
      T hT n (n + 1) rfl).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C n).map T.mor₂)

private lemma isLE_obj_of_uniform_cohomology_bound
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    (R : DerivedCategory A ⥤ DerivedCategory C) [R.CommShift ℤ]
    (P : ObjectProperty (DerivedCategory A))
    (hshift : ∀ (E : DerivedCategory A) (a : ℤ), P E → P (E⟦a⟧))
    (N : ℤ)
    (hbound : ∀ (E : DerivedCategory A), P E → E.IsLE 0 →
      ∀ n : ℤ, N ≤ n → IsZero ((DerivedCategory.homologyFunctor C n).obj (R.obj E)))
    (E : DerivedCategory A) (hE : P E) (a : ℤ) [E.IsLE a] :
    (R.obj E).IsLE (a + N - 1) := by
  have : (E⟦a⟧).IsLE 0 := DerivedCategory.TStructure.t.isLE_shift E a a 0
  have : (R.obj (E⟦a⟧)).IsLE (N - 1) := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    exact hbound _ (hshift E a hE) inferInstance n (by omega)
  have : (R.obj E⟦a⟧).IsLE (N - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (show R.obj (E⟦a⟧) ≅ (R.obj E)⟦a⟧ from (R.commShiftIso a).app E) (N - 1)
  exact DerivedCategory.TStructure.t.isLE_of_shift (R.obj E) (a + N - 1) a (N - 1)

private lemma isIso_homology_map_truncGE_of_uniform_cohomology_bound
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    (R : DerivedCategory A ⥤ DerivedCategory C) [R.CommShift ℤ] [R.IsTriangulated]
    (P : ObjectProperty (DerivedCategory A))
    (hshift : ∀ (E : DerivedCategory A) (a : ℤ), P E → P (E⟦a⟧))
    (htrunc : ∀ (E : DerivedCategory A) (a : ℤ), P E →
      P ((DerivedCategory.TStructure.t.truncLE a).obj E))
    (N : ℤ)
    (hbound : ∀ (E : DerivedCategory A), P E → E.IsLE 0 →
      ∀ n : ℤ, N ≤ n → IsZero ((DerivedCategory.homologyFunctor C n).obj (R.obj E)))
    (E : DerivedCategory A) (hE : P E) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C n).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (n - N + 1)).app E))) := by
  let K := (DerivedCategory.TStructure.t.truncLE (n - N + 1 - 1)).obj E
  have hK : P K := htrunc E _ hE
  have hR : (R.obj K).IsLE (n - N + 1 - 1 + N - 1) :=
    isLE_obj_of_uniform_cohomology_bound R P hshift N hbound K hK _
  apply isIso_homology_map_truncGE_of_isZero
  · exact (R.obj K).isZero_of_isLE (n - N + 1 - 1 + N - 1) n (by omega)
  · exact (R.obj K).isZero_of_isLE (n - N + 1 - 1 + N - 1) (n + 1) (by omega)

private lemma preservesColimitsOfShape_of_inverted_unit
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    (T : C ⥤ C) (η : 𝟭 C ⟶ T) (F : C ⥤ D)
    (hη : ∀ X, IsIso (F.map (η.app X)))
    [PreservesColimitsOfShape J (T ⋙ F)] : PreservesColimitsOfShape J F := by
  let e : F ⟶ T ⋙ F := (Functor.leftUnitor F).inv ≫ Functor.whiskerRight η F
  have : ∀ X, IsIso (e.app X) := by
    intro X
    dsimp [e]
    have := hη X
    infer_instance
  have : IsIso e := NatIso.isIso_of_isIso_app e
  exact preservesColimitsOfShape_of_natIso (asIso e).symm

private lemma preservesColimitsOfShape_of_obj_isZero
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [HasZeroObject D] [HasZeroMorphisms D] (F : C ⥤ D)
    (hF : ∀ X, IsZero (F.obj X)) : PreservesColimitsOfShape J F := by
  refine ⟨fun {K} => ⟨fun {c} _ => ⟨?_⟩⟩⟩
  exact IsColimit.ofIsZero _ ((K ⋙ F).isZero_iff.mpr fun j => hF (K.obj j)) (hF c.pt)

private lemma truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (I : Type i) [HasCoproductsOfShape I (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I)
      ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let T := DerivedCategory.TStructure.t (C := A)
  have hn (n : ℤ) : PreservesColimitsOfShape (Discrete I)
      (T.truncGE a ⋙ DerivedCategory.homologyFunctor A n) := by
    by_cases hna : n < a
    · exact preservesColimitsOfShape_of_obj_isZero _ fun E =>
        ((T.truncGE a).obj E).isZero_of_isGE a n hna
    · let H := DerivedCategory.homologyFunctor A n
      let η : H ⟶ T.truncGE a ⋙ H :=
        (Functor.leftUnitor H).inv ≫ Functor.whiskerRight (T.truncGEπ a) H
      have hη (E : DerivedCategory A) : IsIso (η.app E) := by
        show IsIso (𝟙 _ ≫ H.map ((T.truncGEπ a).app E))
        rw [Category.id_comp]
        apply isIso_homology_map_truncGE_of_isZero (𝟭 (DerivedCategory A)) E a n
        · exact ((T.truncLE (a - 1)).obj E).isZero_of_isLE (a - 1) n (by omega)
        · exact ((T.truncLE (a - 1)).obj E).isZero_of_isLE (a - 1) (n + 1) (by omega)
      have : IsIso η := NatIso.isIso_of_isIso_app η
      exact preservesColimitsOfShape_of_natIso (asIso η)
  apply preservesColimitsOfShape_of_jointlyReflects (T.truncGE a)
    (fun n : ℤ => DerivedCategory.homologyFunctor A n)
  exact ⟨fun f => (DerivedCategory.isIso_iff A f).2 inferInstance⟩

/-- **An exact functor with a uniform bound on a subcategory commutes with its direct sums as
soon as it commutes with the uniformly bounded below ones.** Let `𝒫 ⊆ D(A)` be closed under
shifts and truncations, with direct sums computed in `D(A)`, and suppose `H^n(R(E)) = 0` for
`n ≥ N` whenever `E ∈ 𝒫` lies in `D^{≤ 0}`. If `R` commutes with the direct sum of every family
in `𝒫` lying in degrees `≥ a` for one `a`, then `R` restricted to `𝒫` commutes with direct sums:
`H^n(R(E)) = H^n(R(τ_{≥ n - N + 1} E))` for `E ∈ 𝒫`. -/
theorem preservesColimitsOfShape_ι_comp_of_bounded_of_uniform_bound
    {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory C]
    (P : ObjectProperty (DerivedCategory A))
    (R : DerivedCategory A ⥤ DerivedCategory C) [R.CommShift ℤ] [R.IsTriangulated]
    (I : Type i)
    [HasCoproductsOfShape I (DerivedCategory A)]
    [HasCoproductsOfShape I (DerivedCategory C)]
    [HasCoproductsOfShape I P.FullSubcategory]
    [PreservesColimitsOfShape (Discrete I) P.ι]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor C n)]
    (hshift : ∀ (E : DerivedCategory A) (a : ℤ), P E → P (E⟦a⟧))
    (htruncLE : ∀ (E : DerivedCategory A) (a : ℤ), P E →
      P ((DerivedCategory.TStructure.t.truncLE a).obj E))
    (htruncGE : ∀ (E : DerivedCategory A) (a : ℤ), P E →
      P ((DerivedCategory.TStructure.t.truncGE a).obj E))
    (N : ℤ)
    (hbound : ∀ (E : DerivedCategory A), P E → E.IsLE 0 →
      ∀ n : ℤ, N ≤ n → IsZero ((DerivedCategory.homologyFunctor C n).obj (R.obj E)))
    (hbounded : ∀ (K : I → P.FullSubcategory) (a : ℤ),
      (∀ i, (K i).obj.IsGE a) → PreservesColimit (Discrete.functor K) (P.ι ⋙ R)) :
    PreservesColimitsOfShape (Discrete I) (P.ι ⋙ R) := by
  let F := P.ι ⋙ R
  have hn (n : ℤ) : PreservesColimitsOfShape (Discrete I)
      (F ⋙ DerivedCategory.homologyFunctor C n) := by
    let a := n - N + 1
    let T : P.FullSubcategory ⥤ P.FullSubcategory :=
      P.lift (P.ι ⋙ DerivedCategory.TStructure.t.truncGE a)
        (fun E => htruncGE E.obj a E.property)
    let η : 𝟭 P.FullSubcategory ⟶ T :=
      { app E := ObjectProperty.homMk
          ((DerivedCategory.TStructure.t.truncGEπ a).app E.obj)
        naturality E E' f := by
          ext
          exact (DerivedCategory.TStructure.t.truncGEπ a).naturality f.hom }
    have : PreservesColimitsOfShape (Discrete I)
        ((DerivedCategory.TStructure.t (C := A)).truncGE a) :=
      truncGE_preservesCoproducts (A := A) I a
    have : PreservesColimitsOfShape (Discrete I) (T ⋙ P.ι) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete I)
        (P.ι ⋙ DerivedCategory.TStructure.t.truncGE a))
    have : PreservesColimitsOfShape (Discrete I) T :=
      preservesColimitsOfShape_of_reflects_of_preserves T P.ι
    have : PreservesColimitsOfShape (Discrete I) (T ⋙ F) := by
      constructor
      intro K
      have : PreservesColimit (K ⋙ T) F := by
        have := hbounded (fun i => T.obj (K.obj ⟨i⟩)) a
          (fun i => by
            show ((DerivedCategory.TStructure.t.truncGE a).obj
              (K.obj ⟨i⟩).obj).IsGE a
            infer_instance)
        exact preservesColimit_of_iso_diagram
          (K₁ := Discrete.functor (fun i => T.obj (K.obj ⟨i⟩))) F
          (Discrete.natIso fun i => Iso.refl _)
      infer_instance
    have : PreservesColimitsOfShape (Discrete I)
        (T ⋙ (F ⋙ DerivedCategory.homologyFunctor C n)) :=
      preservesColimitsOfShape_of_natIso
        (Functor.associator T F (DerivedCategory.homologyFunctor C n))
    apply preservesColimitsOfShape_of_inverted_unit T η
    intro E
    exact isIso_homology_map_truncGE_of_uniform_cohomology_bound
      R P hshift htruncLE N hbound E.obj E.property n
  apply preservesColimitsOfShape_of_jointlyReflects F
    (fun n : ℤ => DerivedCategory.homologyFunctor C n)
  exact ⟨fun f => (DerivedCategory.isIso_iff C f).2 inferInstance⟩

/-- **The right derived functor, restricted to a subcategory with a uniform bound, commutes with
direct sums.** Let `F : A ⥤ C` be left exact out of a Grothendieck abelian category, with right
derived functor `RF`, and suppose every `R^q F` commutes with direct sums indexed by `I`. Let
`𝒫 ⊆ D(A)` be closed under shifts and under the truncations `τ_{≤ a}`, `τ_{≥ a}`, with direct sums
computed in `D(A)`, and suppose there is `N` with `H^n(RF(E)) = 0` for `n ≥ N` and every
`E ∈ 𝒫 ∩ D^{≤ 0}`. Then `RF` restricted to `𝒫` commutes with direct sums indexed by `I`. -/
theorem preservesColimitsOfShape_ι_comp_of_uniform_bound
    [IsGrothendieckAbelian.{i} A] (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory C) [RF.CommShift ℤ] [RF.IsTriangulated]
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (P : ObjectProperty (DerivedCategory A)) (I : Type i)
    [HasCoproductsOfShape I C]
    [HasCoproductsOfShape I (DerivedCategory A)] [HasCoproductsOfShape I (DerivedCategory C)]
    [HasCoproductsOfShape I P.FullSubcategory] [PreservesColimitsOfShape (Discrete I) P.ι]
    [PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A))]
    [PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := C))]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor C n)]
    (hshift : ∀ (E : DerivedCategory A) (a : ℤ), P E → P (E⟦a⟧))
    (htruncLE : ∀ (E : DerivedCategory A) (a : ℤ), P E →
      P ((DerivedCategory.TStructure.t.truncLE a).obj E))
    (htruncGE : ∀ (E : DerivedCategory A) (a : ℤ), P E →
      P ((DerivedCategory.TStructure.t.truncGE a).obj E))
    (N : ℤ)
    (hbound : ∀ (E : DerivedCategory A), P E → E.IsLE 0 →
      ∀ n : ℤ, N ≤ n → IsZero ((DerivedCategory.homologyFunctor C n).obj (RF.obj E)))
    (hcoproducts : ∀ q : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived q)) :
    PreservesColimitsOfShape (Discrete I) (P.ι ⋙ RF) := by
  apply preservesColimitsOfShape_ι_comp_of_bounded_of_uniform_bound
    P RF I hshift htruncLE htruncGE N hbound
  intro K a hK
  have : PreservesColimit (Discrete.functor (fun j => (K j).obj)) RF :=
    preservesColimit_of_forall_isGE F I hcoproducts RF α _ a hK
  have : PreservesColimit (Discrete.functor K ⋙ P.ι) RF :=
    preservesColimit_of_iso_diagram (K₁ := Discrete.functor (fun j => (K j).obj)) RF
      (Discrete.natIso fun j => Iso.refl _)
  infer_instance

end BoundedBelow

end Stacks.DerivedFunctor.Coproducts
