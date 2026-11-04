module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.Topology.Sheaves.Sheaf.Constant

/-!
# Meromorphic functions on an integral scheme

On an integral scheme `X` the sheaf of meromorphic functions — the sheaf of total quotient
rings of the structure sheaf — is the constant sheaf on the function field of `X`. Moreover the
identification sends a regular function to the constant function given by its germ at the
generic point.

## Main results

* `AlgebraicGeometry.nonempty_totalQuotientSheafIsoConstant` and
  `AlgebraicGeometry.totalQuotientSheafIsoConstant`: the sheaf of total quotient rings of an
  integral scheme is isomorphic, as a sheaf of commutative rings, to the constant sheaf on the
  function field, by an isomorphism which carries a regular section to the constant section
  determined by its germ at the generic point.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-! ### The total quotient presheaf of an integral scheme -/

/-- The denominators of the total quotient presheaf on an open set: the sections whose germ at
every point of that open set is a nonzerodivisor. -/
private noncomputable abbrev totalQuotientDenominators (X : Scheme.{u})
    (U : X.Opens) : Submonoid Γ(X, U) :=
  (X.presheaf.submonoidPresheafOfStalk
    (fun x ↦ (X.presheaf.stalk x)⁰)).obj (Opposite.op U)

/-- A nonempty open subset of an irreducible scheme contains the generic point. -/
private lemma genericPoint_mem_of_nonempty (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The germs at the generic point of the denominators are units in the function field. -/
private lemma isUnit_germToFunctionField_denominator (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (y : totalQuotientDenominators X U) :
    IsUnit ((X.germToFunctionField U).hom y) :=
  isUnit_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp
    ((Submonoid.mem_iInf.mp y.2) ⟨genericPoint X, genericPoint_mem_of_nonempty X U⟩))

private lemma totalQuotientDenominators_eq_nonZeroDivisors (X : Scheme.{u})
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    totalQuotientDenominators X U = nonZeroDivisors Γ(X, U) := by
  classical
  ext s
  show s ∈ (X.presheaf.submonoidPresheafOfStalk
    (fun x ↦ (X.presheaf.stalk x)⁰)).obj (Opposite.op U) ↔
      s ∈ nonZeroDivisors Γ(X, U)
  simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj,
    Submonoid.mem_iInf, Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · intro hs hzero
    exact hs ⟨genericPoint X, genericPoint_mem_of_nonempty X U⟩ (by simp [hzero])
  · intro hs x
    exact fun hx ↦ hs (AlgebraicGeometry.germ_injective_of_isIntegral X x.1 x.2
      (by simpa using hx))

private noncomputable def totalQuotientOpenFunctionFieldEquiv (X : Scheme.{u})
    [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Localization (totalQuotientDenominators X U) ≃ₐ[Γ(X, U)] X.functionField := by
  let M := totalQuotientDenominators X U
  have hM : M = nonZeroDivisors Γ(X, U) := totalQuotientDenominators_eq_nonZeroDivisors X U
  letI : Algebra Γ(X, U) (Localization M) := inferInstance
  letI : IsLocalization M (Localization M) := inferInstance
  letI : Algebra Γ(X, U) X.functionField := (X.germToFunctionField U).hom.toAlgebra
  have hK : IsLocalization M X.functionField := by
    rw [hM]
    exact AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsLocalization M X.functionField := hK
  exact IsLocalization.algEquiv M (Localization M) X.functionField

private noncomputable def totalQuotientOpenToFunctionFieldRingHom (X : Scheme.{u})
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Localization (totalQuotientDenominators X U) →+* X.functionField := by
  let M := totalQuotientDenominators X U
  letI : Algebra Γ(X, U) (Localization M) := inferInstance
  letI : IsLocalization M (Localization M) := inferInstance
  letI : Algebra Γ(X, U) X.functionField := (X.germToFunctionField U).hom.toAlgebra
  let g : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  have hg : ∀ y : M, IsUnit (g y) := isUnit_germToFunctionField_denominator X U
  exact IsLocalization.lift (M := M) (g := g) hg

private noncomputable def totalQuotientOpenToFunctionField (X : Scheme.{u})
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    CommRingCat.Hom ((X.presheaf.totalQuotientPresheaf).obj (Opposite.op U))
      X.functionField :=
  CommRingCat.ofHom (totalQuotientOpenToFunctionFieldRingHom X U)

private lemma totalQuotientOpenToFunctionField_algebraMap_localization (X : Scheme.{u})
    [IsIntegral X] (U : X.Opens) [Nonempty U] (s : Γ(X, U)) :
    (totalQuotientOpenToFunctionField X U).hom
        (algebraMap Γ(X, U) (Localization (totalQuotientDenominators X U)) s) =
      (X.germToFunctionField U).hom s := by
  let M := totalQuotientDenominators X U
  let : Algebra Γ(X, U) (Localization M) := inferInstance
  let : IsLocalization M (Localization M) := Localization.isLocalization
  let : Algebra Γ(X, U) X.functionField := (X.germToFunctionField U).hom.toAlgebra
  let g : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  have hg : ∀ y : M, IsUnit (g y) := isUnit_germToFunctionField_denominator X U
  show (IsLocalization.lift (M := M) (g := g) hg)
      (algebraMap Γ(X, U) (Localization M) s) = g s
  exact IsLocalization.lift_eq hg s

private lemma totalQuotientOpenToFunctionFieldRingHom_bijective (X : Scheme.{u})
    [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Bijective (totalQuotientOpenToFunctionFieldRingHom X U) := by
  let e := totalQuotientOpenFunctionFieldEquiv X U hU
  have he : totalQuotientOpenToFunctionFieldRingHom X U = e.toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (totalQuotientDenominators X U)
    ext s
    show (totalQuotientOpenToFunctionField X U).hom
        (algebraMap Γ(X, U) (Localization (totalQuotientDenominators X U)) s) = _
    rw [totalQuotientOpenToFunctionField_algebraMap_localization]
    simp [e, totalQuotientOpenFunctionFieldEquiv, RingHom.algebraMap_toAlgebra]
  rw [he]
  exact e.toRingEquiv.bijective

private lemma totalQuotientOpenToFunctionField_naturality (X : Scheme.{u})
    [IsIntegral X] {U V : X.Opens} (hUV : U ≤ V) [Nonempty U] [Nonempty V] :
    (totalQuotientOpenToFunctionFieldRingHom X U).comp
        (IsLocalization.map (Localization (totalQuotientDenominators X U))
          (X.presheaf.map (homOfLE hUV).op).hom
          ((X.presheaf.submonoidPresheafOfStalk
            (fun x ↦ (X.presheaf.stalk x)⁰)).map (homOfLE hUV).op)) =
      totalQuotientOpenToFunctionFieldRingHom X V := by
  let G := X.presheaf.submonoidPresheafOfStalk
    (fun x ↦ (X.presheaf.stalk x)⁰)
  let Mv := G.obj (Opposite.op V)
  let Mu := G.obj (Opposite.op U)
  have hG := G.map (homOfLE hUV).op
  apply IsLocalization.ringHom_ext Mv
  ext s
  rw [RingHom.comp_assoc, IsLocalization.map_comp]
  show (totalQuotientOpenToFunctionFieldRingHom X U)
      (algebraMap Γ(X, U) (Localization Mu)
        ((X.presheaf.map (homOfLE hUV).op).hom s)) =
    (totalQuotientOpenToFunctionFieldRingHom X V)
      (algebraMap Γ(X, V) (Localization Mv) s)
  show (totalQuotientOpenToFunctionField X U).hom _ =
    (totalQuotientOpenToFunctionField X V).hom _
  rw [totalQuotientOpenToFunctionField_algebraMap_localization,
    totalQuotientOpenToFunctionField_algebraMap_localization]
  simp [Scheme.germToFunctionField, X.presheaf.germ_res_apply]

private noncomputable def totalQuotientGenericStalkCocone (X : Scheme.{u})
    [IsIntegral X] :
    Cocone ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf.totalQuotientPresheaf) := by
  let P := X.presheaf.totalQuotientPresheaf
  exact {
    pt := X.functionField
    ι := {
      app := fun U => by
        letI : Nonempty U.unop.1 := by
          simpa using ((genericPoint_spec X).mem_open_set_iff U.unop.1.2).mp U.unop.2
        exact totalQuotientOpenToFunctionField X U.unop.1
      naturality := fun U V inc => by
        let : Nonempty U.unop.1 := by
          simpa using ((genericPoint_spec X).mem_open_set_iff U.unop.1.2).mp U.unop.2
        let : Nonempty V.unop.1 := by
          simpa using ((genericPoint_spec X).mem_open_set_iff V.unop.1.2).mp V.unop.2
        apply CommRingCat.hom_ext
        exact totalQuotientOpenToFunctionField_naturality X inc.unop.le
    }
  }

private noncomputable def totalQuotientGenericStalkHom (X : Scheme.{u}) [IsIntegral X] :
    (X.presheaf.totalQuotientPresheaf).stalk (genericPoint X) ⟶ X.functionField :=
  colimit.desc _ (totalQuotientGenericStalkCocone X)

private lemma totalQuotientGenericStalkHom_germ (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (hU : genericPoint X ∈ U) :
    (X.presheaf.totalQuotientPresheaf).germ U (genericPoint X) hU ≫
      totalQuotientGenericStalkHom X = totalQuotientOpenToFunctionField X U := by
  show colimit.ι _ (op ⟨U, hU⟩) ≫ colimit.desc _
    (totalQuotientGenericStalkCocone X) = _
  rw [colimit.ι_desc]
  rfl

private noncomputable def totalQuotientToGenericSkyscraperPresheaf (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)] :
    X.presheaf.totalQuotientPresheaf ⟶
      skyscraperPresheaf (genericPoint X) X.functionField :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
    (genericPoint X) (totalQuotientGenericStalkHom X)

private lemma totalQuotientToGenericSkyscraperPresheaf_app (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)]
    (U : X.Opens) [Nonempty U] (hU : genericPoint X ∈ U) :
    (totalQuotientToGenericSkyscraperPresheaf X).app (op U) ≫
        eqToHom (ite_eq_left hU) = totalQuotientOpenToFunctionField X U := by
  calc
    (totalQuotientToGenericSkyscraperPresheaf X).app (op U) ≫ eqToHom (ite_eq_left hU) =
        (X.presheaf.totalQuotientPresheaf).germ U (genericPoint X) hU ≫
          StalkSkyscraperPresheafAdjunctionAuxs.fromStalk (genericPoint X)
            (totalQuotientToGenericSkyscraperPresheaf X) :=
      (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
        (genericPoint X) (totalQuotientToGenericSkyscraperPresheaf X) U hU).symm
    _ = (X.presheaf.totalQuotientPresheaf).germ U (genericPoint X) hU ≫
          totalQuotientGenericStalkHom X := by
      rw [totalQuotientToGenericSkyscraperPresheaf,
        StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper]
    _ = totalQuotientOpenToFunctionField X U := totalQuotientGenericStalkHom_germ X U hU

private lemma totalQuotientToGenericSkyscraperPresheaf_app_isIso (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIso ((totalQuotientToGenericSkyscraperPresheaf X).app (op U)) := by
  have hη := genericPoint_mem_of_nonempty X U
  have hcomp := totalQuotientToGenericSkyscraperPresheaf_app X U hη
  have hcompIso : IsIso ((totalQuotientToGenericSkyscraperPresheaf X).app (op U) ≫
      eqToHom (ite_eq_left hη)) := by
    rw [hcomp]
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (totalQuotientOpenToFunctionFieldRingHom_bijective X U hU)
  have hcast : IsIso (eqToHom (ite_eq_left hη) :
      (skyscraperPresheaf (genericPoint X) X.functionField).obj (op U) ⟶
        CommRingCat.of X.functionField) := (eqToIso (ite_eq_left hη)).isIso_hom
  let := hcast
  exact IsIso.of_isIso_comp_right
    ((totalQuotientToGenericSkyscraperPresheaf X).app (op U))
    (eqToHom (ite_eq_left hη))

/-- A morphism from a presheaf to the skyscraper presheaf at the generic point of an integral
scheme is bijective on stalks if it is an isomorphism over every nonempty affine open. -/
private lemma stalk_map_bijective_of_isIso_app_nonempty_affineOpen (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)]
    (F : TopCat.Presheaf CommRingCat X)
    (α : F ⟶ skyscraperPresheaf (genericPoint X) X.functionField)
    (hα : ∀ U : X.Opens, IsAffineOpen U → Nonempty U → IsIso (α.app (op U))) (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α) := by
  classical
  let B : Set (Opens X) := {U | U ∈ X.affineOpens ∧ Nonempty U}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    rintro U y hy
    obtain ⟨V, hV, hyV, hVU⟩ :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact ⟨V, ⟨hV, ⟨⟨y, hyV⟩⟩⟩, hyV, hVU⟩
  refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun U hUB ↦ ?_) x, ?_⟩
  · have := hα U hUB.1 hUB.2
    exact (ConcreteCategory.bijective_of_isIso (α.app (op U))).1
  · intro t
    obtain ⟨U, hxU, hUB, tU, ht⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB
        (skyscraperPresheaf (genericPoint X) X.functionField) x t
    have := hα U hUB.1 hUB.2
    obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (α.app (op U))).2 tU
    refine ⟨(TopCat.Presheaf.germ (C := CommRingCat) (X := X) F U x hxU).hom s, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs, ht]

private lemma totalQuotientToGenericSkyscraperPresheaf_stalk_bijective (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)] (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (totalQuotientToGenericSkyscraperPresheaf X)) :=
  stalk_map_bijective_of_isIso_app_nonempty_affineOpen X _ _
    (fun U hU _ ↦ totalQuotientToGenericSkyscraperPresheaf_app_isIso X U hU) x

private noncomputable def totalQuotientToGenericSkyscraper (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)] :
    totalQuotientSheaf X.sheaf ⟶
      skyscraperSheaf (genericPoint X) X.functionField :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map
    (totalQuotientToGenericSkyscraperPresheaf X) ≫
      (sheafificationIso (skyscraperSheaf (genericPoint X) X.functionField)).inv

private lemma stalk_map_presheafToSheaf_map_isIso {X : TopCat.{u}}
    (F G : TopCat.Presheaf CommRingCat X) (α : F ⟶ G)
    (hα : ∀ x, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α)) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map α).hom) := by
  let J := Opens.grothendieckTopology X
  let β := (presheafToSheaf J CommRingCat).map α
  have hnat : α ≫ toSheafify J G = toSheafify J F ≫ β.hom :=
    CategoryTheory.toSheafify_naturality J α
  have hunitF : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toSheafify J F)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat F
  have hunitG : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toSheafify J G)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat G
  have hEq := congrArg ((TopCat.Presheaf.stalkFunctor CommRingCat x).map) hnat
  simp only [Functor.map_comp] at hEq
  have hright : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toSheafify J F) ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map β.hom) := by
    rw [← hEq]
    infer_instance
  let : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toSheafify J F) ≫ (TopCat.Presheaf.stalkFunctor CommRingCat x).map β.hom) := hright
  exact IsIso.of_isIso_comp_left
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (toSheafify J F))
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map β.hom)

private lemma totalQuotientToGenericSkyscraper_isIso (X : Scheme.{u}) [IsIntegral X]
    [∀ U : Opens X, Decidable (genericPoint X ∈ U)] :
    IsIso (totalQuotientToGenericSkyscraper X) := by
  classical
  let β := (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map
    (totalQuotientToGenericSkyscraperPresheaf X)
  have hβ : IsIso β := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso β).2
    intro y
    exact stalk_map_presheafToSheaf_map_isIso
      (X.presheaf.totalQuotientPresheaf)
      (skyscraperPresheaf (genericPoint X) X.functionField)
      (totalQuotientToGenericSkyscraperPresheaf X)
      (fun z ↦ (ConcreteCategory.isIso_iff_bijective _).2
        (totalQuotientToGenericSkyscraperPresheaf_stalk_bijective X z)) y
  let e := sheafificationIso (skyscraperSheaf (genericPoint X) X.functionField)
  show IsIso (β ≫ e.inv)
  exact IsIso.comp_isIso' hβ e.isIso_inv

/-! ### The constant presheaf on the function field -/

private noncomputable def constantGenericStalkCocone (X : Scheme.{u}) [IsIntegral X] :
    Cocone ((OpenNhds.inclusion (genericPoint X)).op ⋙
      (Functor.const (Opens X)ᵒᵖ).obj X.functionField) := by
  refine { pt := X.functionField, ι := ?_ }
  refine { app := fun _ => 𝟙 X.functionField, naturality := ?_ }
  intro U V f
  simp

private noncomputable def constantGenericStalkHom (X : Scheme.{u}) [IsIntegral X] :
    TopCat.Presheaf.stalk (C := CommRingCat) (X := X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) (genericPoint X) ⟶
      X.functionField :=
  colimit.desc _ (constantGenericStalkCocone X)

private lemma constantGenericStalkHom_germ (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    TopCat.Presheaf.germ (C := CommRingCat) (X := X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) U
      (genericPoint X) hU ≫ constantGenericStalkHom X = 𝟙 X.functionField := by
  show colimit.ι _ (op ⟨U, hU⟩) ≫ colimit.desc _ (constantGenericStalkCocone X) = _
  rw [colimit.ι_desc]
  rfl

private noncomputable def constantToGenericSkyscraperPresheaf (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)] :
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField ⟶
      skyscraperPresheaf (genericPoint X) X.functionField :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
    (genericPoint X) (constantGenericStalkHom X)

private lemma constantToGenericSkyscraperPresheaf_app (X : Scheme.{u}) [IsIntegral X]
    [∀ U : Opens X, Decidable (genericPoint X ∈ U)] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    (constantToGenericSkyscraperPresheaf X).app (op U) ≫ eqToHom (ite_eq_left hU) =
      TopCat.Presheaf.germ (C := CommRingCat) (X := X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) U
        (genericPoint X) hU ≫ constantGenericStalkHom X := by
  calc
    _ = TopCat.Presheaf.germ (C := CommRingCat) (X := X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) U (genericPoint X) hU ≫
        StalkSkyscraperPresheafAdjunctionAuxs.fromStalk (genericPoint X)
          (constantToGenericSkyscraperPresheaf X) :=
      (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
        (genericPoint X) (constantToGenericSkyscraperPresheaf X) U hU).symm
    _ = TopCat.Presheaf.germ (C := CommRingCat) (X := X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) U (genericPoint X) hU ≫
          constantGenericStalkHom X := by
      rw [constantToGenericSkyscraperPresheaf,
        StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper]

private lemma constantToGenericSkyscraperPresheaf_app_isIso (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)]
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    IsIso ((constantToGenericSkyscraperPresheaf X).app (op U)) := by
  have hcomp : (constantToGenericSkyscraperPresheaf X).app (op U) ≫
      eqToHom (ite_eq_left hU) = 𝟙 X.functionField := by
    calc
      _ = TopCat.Presheaf.germ (C := CommRingCat) (X := X)
            ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) U
            (genericPoint X) hU ≫ constantGenericStalkHom X :=
        constantToGenericSkyscraperPresheaf_app X U hU
      _ = 𝟙 X.functionField := constantGenericStalkHom_germ X U hU
  have hcast : IsIso (eqToHom (ite_eq_left hU) :
      (skyscraperPresheaf (genericPoint X) X.functionField).obj (op U) ⟶
        X.functionField) := (eqToIso (ite_eq_left hU)).isIso_hom
  let : IsIso (𝟙 X.functionField) := (Iso.refl _).isIso_hom
  let : IsIso ((constantToGenericSkyscraperPresheaf X).app (op U) ≫
      eqToHom (ite_eq_left hU)) := by rw [hcomp]; infer_instance
  let := hcast
  exact IsIso.of_isIso_comp_right
    ((constantToGenericSkyscraperPresheaf X).app (op U)) (eqToHom (ite_eq_left hU))

private lemma constantToGenericSkyscraperPresheaf_stalk_bijective (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)] (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (constantToGenericSkyscraperPresheaf X)) :=
  stalk_map_bijective_of_isIso_app_nonempty_affineOpen X _ _
    (fun U _ _ ↦ constantToGenericSkyscraperPresheaf_app_isIso X U
      (genericPoint_mem_of_nonempty X U)) x

private noncomputable def constantToGenericSkyscraper (X : Scheme.{u})
    [IsIntegral X] [∀ U : Opens X, Decidable (genericPoint X ∈ U)] :
    constantSheafOnSpace X CommRingCat X.functionField ⟶
      skyscraperSheaf (genericPoint X) X.functionField := by
  let γ := constantToGenericSkyscraperPresheaf X
  exact (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map γ ≫
    (sheafificationIso (skyscraperSheaf (genericPoint X) X.functionField)).inv

private lemma constantToGenericSkyscraper_isIso (X : Scheme.{u}) [IsIntegral X]
    [∀ U : Opens X, Decidable (genericPoint X ∈ U)] :
    IsIso (constantToGenericSkyscraper X) := by
  classical
  let α := constantToGenericSkyscraperPresheaf X
  let β := (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map α
  have hβ : IsIso β := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso β).2
    intro x
    exact stalk_map_presheafToSheaf_map_isIso
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)
      (skyscraperPresheaf (genericPoint X) X.functionField) α
      (fun y ↦ (ConcreteCategory.isIso_iff_bijective _).2
        (constantToGenericSkyscraperPresheaf_stalk_bijective X y)) x
  let e := sheafificationIso (skyscraperSheaf (genericPoint X) X.functionField)
  show IsIso (β ≫ e.inv)
  exact IsIso.comp_isIso' hβ e.isIso_inv

private lemma constantToGenericSkyscraper_toSheafify_app (X : Scheme.{u}) [IsIntegral X]
    [∀ U : Opens X, Decidable (genericPoint X ∈ U)] (U : X.Opens)
    (hU : genericPoint X ∈ U) (a : X.functionField) :
    (((eqToHom (ite_eq_left hU) :
      (skyscraperPresheaf (genericPoint X) X.functionField).obj (op U) ⟶
        X.functionField).hom)
      (((constantToGenericSkyscraper X).hom.app (op U)).hom
        (((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)).hom a))) = a := by
  classical
  let F := (Functor.const (Opens X)ᵒᵖ).obj X.functionField
  let P := skyscraperPresheaf (genericPoint X) X.functionField
  let γ := constantToGenericSkyscraperPresheaf X
  let β := (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map γ
  let σ := sheafificationIso (skyscraperSheaf (genericPoint X) X.functionField)
  let hP := (skyscraperSheaf (genericPoint X) X.functionField).property
  have hNat : (β.hom.app (op U)).hom
        (((toSheafify (Opens.grothendieckTopology X) F).app (op U)).hom a) =
      ((toSheafify (Opens.grothendieckTopology X) P).app (op U)).hom
        ((γ.app (op U)).hom a) := by
    have h := congrArg (fun q => (q.app (op U)).hom a)
      (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X) γ)
    simpa only [NatTrans.comp_app, CommRingCat.comp_apply] using h.symm
  have hUnit (b : (P.obj (op U))) :
      (σ.inv.hom.app (op U)).hom
        (((toSheafify (Opens.grothendieckTopology X) P).app (op U)).hom b) = b := by
    show ((isoSheafify (Opens.grothendieckTopology X) hP).inv.app (op U)).hom
        (((toSheafify (Opens.grothendieckTopology X) P).app (op U)).hom b) = b
    rw [isoSheafify_inv]
    have h := congrArg (fun q => (q.app (op U)).hom b)
      (toSheafify_sheafifyLift (Opens.grothendieckTopology X) (𝟙 P) hP)
    show ((sheafifyLift (Opens.grothendieckTopology X) (𝟙 P) hP).app (op U)).hom
        (((toSheafify (Opens.grothendieckTopology X) P).app (op U)).hom b) =
      ((𝟙 P : P ⟶ P).app (op U)).hom b
    exact h
  have hGamma : (eqToHom (ite_eq_left hU) : P.obj (op U) ⟶ X.functionField).hom
      ((γ.app (op U)).hom a) = a := by
    have h1 := congrArg (fun q => q.hom a)
      (constantToGenericSkyscraperPresheaf_app X U hU)
    have h2 := congrArg (fun q => q.hom a)
      (constantGenericStalkHom_germ X U hU)
    simpa [CommRingCat.comp_apply] using h1.trans h2
  show (eqToHom (ite_eq_left hU) : P.obj (op U) ⟶ CommRingCat.of X.functionField).hom
      ((σ.inv.hom.app (op U)).hom
        ((β.hom.app (op U)).hom
          (((toSheafify (Opens.grothendieckTopology X) F).app (op U)).hom a))) = a
  rw [hNat, hUnit, hGamma]

private lemma totalQuotientToGenericSkyscraper_toTotalQuotient_app (X : Scheme.{u})
    [IsIntegral X]
    [∀ U : Opens X, Decidable (genericPoint X ∈ U)] (U : X.Opens)
    [Nonempty U] (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    ((eqToHom (ite_eq_left hU) :
      (skyscraperSheaf (genericPoint X) X.functionField).obj.obj (op U) ⟶
        X.functionField).hom)
      (((totalQuotientToGenericSkyscraper X).hom.app (op U)).hom
        (((toTotalQuotientSheaf X.sheaf).hom.app (op U)).hom s)) =
      (X.germToFunctionField U).hom s := by
  classical
  let J := Opens.grothendieckTopology X
  let Q := X.presheaf.totalQuotientPresheaf
  let τ := X.presheaf.toTotalQuotientPresheaf
  let α := totalQuotientToGenericSkyscraperPresheaf X
  let P := skyscraperPresheaf (genericPoint X) X.functionField
  let σ := sheafificationIso (skyscraperSheaf (genericPoint X) X.functionField)
  have hnatα : ((sheafifyMap J α).app (op U)).hom
      (((toSheafify J Q).app (op U)).hom ((τ.app (op U)).hom s)) =
      ((toSheafify J P).app (op U)).hom
        ((α.app (op U)).hom ((τ.app (op U)).hom s)) := by
    have h := congrArg (fun q : Q ⟶ sheafify J P =>
      (q.app (op U)).hom ((τ.app (op U)).hom s)) (toSheafify_naturality J α)
    simpa only [NatTrans.comp_app, CommRingCat.comp_apply] using h.symm
  show (eqToHom (ite_eq_left hU) : P.obj (op U) ⟶ CommRingCat.of X.functionField).hom
      (((σ.inv.hom.app (op U)).hom
        ((((sheafifyMap J α).app (op U)).hom)
          (((toSheafify J Q).app (op U)).hom ((τ.app (op U)).hom s))))) = _
  rw [hnatα]
  have hUnit : (σ.inv.hom.app (op U)).hom
      (((toSheafify J P).app (op U)).hom
        ((α.app (op U)).hom ((τ.app (op U)).hom s))) =
      (α.app (op U)).hom ((τ.app (op U)).hom s) := by
    show ((isoSheafify J (skyscraperSheaf (genericPoint X) X.functionField).property).inv.app
        (op U)).hom (((toSheafify J P).app (op U)).hom
          ((α.app (op U)).hom ((τ.app (op U)).hom s))) = _
    rw [isoSheafify_inv]
    have hh := congrArg (fun q => (q.app (op U)).hom
        ((α.app (op U)).hom ((τ.app (op U)).hom s)))
      (toSheafify_sheafifyLift J (𝟙 P)
        (skyscraperSheaf (genericPoint X) X.functionField).property)
    show ((sheafifyLift J (𝟙 P)
        (skyscraperSheaf (genericPoint X) X.functionField).property).app
        (op U)).hom (((toSheafify J P).app (op U)).hom
          ((α.app (op U)).hom ((τ.app (op U)).hom s))) =
      ((𝟙 P : P ⟶ P).app (op U)).hom ((α.app (op U)).hom ((τ.app (op U)).hom s))
    exact hh
  rw [hUnit]
  have hpres : (eqToHom (ite_eq_left hU) : P.obj (op U) ⟶
      CommRingCat.of X.functionField).hom ((α.app (op U)).hom ((τ.app (op U)).hom s)) =
      (totalQuotientOpenToFunctionField X U).hom ((τ.app (op U)).hom s) := by
    have hh := congrArg (fun q => q.hom ((τ.app (op U)).hom s))
      (totalQuotientToGenericSkyscraperPresheaf_app X U hU)
    simpa [P, skyscraperSheaf, CommRingCat.comp_apply] using hh
  rw [hpres]
  exact totalQuotientOpenToFunctionField_algebraMap_localization X U s

/-! ### The comparison isomorphism -/

/-- On an integral scheme the sheaf of meromorphic functions — the sheaf of total quotient rings
of the structure sheaf — is isomorphic to the constant sheaf on the function field, by an
isomorphism carrying a regular section to the constant section determined by its germ at the
generic point. -/
theorem nonempty_totalQuotientSheafIsoConstant (X : Scheme.{u}) [IsIntegral X] :
    Nonempty { e : totalQuotientSheaf X.sheaf ≅
        constantSheafOnSpace X CommRingCat.{u} X.functionField //
      ∀ (U : X.Opens) (s : X.presheaf.obj (Opposite.op U))
        (h : genericPoint X ∈ U),
        (e.hom.hom.app (Opposite.op U)).hom
          ((toTotalQuotientSheaf X.sheaf).hom.app (Opposite.op U) s) =
        (toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (Opposite.op U)
            (X.presheaf.germ U (genericPoint X) h s) } := by
  classical
  let f := totalQuotientToGenericSkyscraper X
  let g := constantToGenericSkyscraper X
  have : IsIso f := totalQuotientToGenericSkyscraper_isIso X
  have : IsIso g := constantToGenericSkyscraper_isIso X
  let e : totalQuotientSheaf X.sheaf ≅
      constantSheafOnSpace X CommRingCat X.functionField := asIso f ≪≫ (asIso g).symm
  refine ⟨⟨e, ?_⟩⟩
  intro U s h
  have : IsIso g.hom := by
    show IsIso ((sheafToPresheaf
      (Opens.grothendieckTopology X) CommRingCat).map g)
    exact Functor.map_isIso (sheafToPresheaf
      (Opens.grothendieckTopology X) CommRingCat) g
  have : IsIso (g.hom.app (op U)) := by infer_instance
  apply (ConcreteCategory.bijective_of_isIso (g.hom.app (op U))).1
  show (g.hom.app (op U))
      ((e.hom.hom.app (op U))
        ((toTotalQuotientSheaf X.sheaf).hom.app (op U) s)) =
    (g.hom.app (op U))
      ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)
          (X.presheaf.germ U (genericPoint X) h s))
  dsimp only [e]
  dsimp only [Iso.trans, Iso.symm]
  show (g.hom.app (op U)).hom
      (((asIso g).inv.hom.app (op U)).hom
        ((f.hom.app (op U)).hom
          ((toTotalQuotientSheaf X.sheaf).hom.app (op U) s))) =
    (g.hom.app (op U)).hom
      (((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)).hom
          ((X.presheaf.germ U (genericPoint X) h).hom s))
  let : Nonempty U := ⟨genericPoint X, h⟩
  let v := (f.hom.app (op U)).hom
    ((toTotalQuotientSheaf X.sheaf).hom.app (op U) s)
  have hcancel : (g.hom.app (op U)).hom (((asIso g).inv.hom.app (op U)).hom v) = v := by
    have hcomp : (asIso g).inv.hom.app (op U) ≫ (asIso g).hom.hom.app (op U) = 𝟙 _ :=
      congrArg (fun q => q.hom.app (op U)) (asIso g).inv_hom_id
    have hh := congrArg (fun q => q.hom v) hcomp
    show ((asIso g).hom.hom.app (op U)).hom
      (((asIso g).inv.hom.app (op U)).hom v) = v
    simpa only [CommRingCat.comp_apply, CategoryTheory.id_apply] using hh
  rw [hcancel]
  have : IsIso (eqToHom (ite_eq_left h) :
      (skyscraperSheaf (genericPoint X) X.functionField).obj.obj (op U) ⟶
        CommRingCat.of X.functionField) := (eqToIso (ite_eq_left h)).isIso_hom
  apply (ConcreteCategory.bijective_of_isIso
    (eqToHom (ite_eq_left h) :
      (skyscraperSheaf (genericPoint X) X.functionField).obj.obj (op U) ⟶
        CommRingCat.of X.functionField)).1
  calc
    _ = (X.germToFunctionField U).hom s :=
      totalQuotientToGenericSkyscraper_toTotalQuotient_app X U h s
    _ = ((eqToHom (ite_eq_left h) :
          (skyscraperSheaf (genericPoint X) X.functionField).obj.obj (op U) ⟶
            CommRingCat.of X.functionField).hom)
        ((g.hom.app (op U)).hom
          (((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)).hom
              ((X.presheaf.germ U (genericPoint X) h).hom s))) :=
      (constantToGenericSkyscraper_toSheafify_app X U h ((X.germToFunctionField U).hom s)).symm

/-- An isomorphism between the sheaf of meromorphic functions on an integral scheme and the
constant sheaf on its function field, carrying a regular section to the constant section
determined by its germ at the generic point. -/
@[stacks 01X5 "part (1)", ega "I 7.3.6" "F = O_X, integral"]
noncomputable def totalQuotientSheafIsoConstant (X : Scheme.{u}) [IsIntegral X] :
    { e : totalQuotientSheaf X.sheaf ≅
        constantSheafOnSpace X CommRingCat.{u} X.functionField //
      ∀ (U : X.Opens) (s : X.presheaf.obj (Opposite.op U))
        (h : genericPoint X ∈ U),
        (e.hom.hom.app (Opposite.op U)).hom
          ((toTotalQuotientSheaf X.sheaf).hom.app (Opposite.op U) s) =
        (toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (Opposite.op U)
            (X.presheaf.germ U (genericPoint X) h s) } :=
  Classical.choice (nonempty_totalQuotientSheafIsoConstant X)

end AlgebraicGeometry

end
