module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The mapping telescope

For a sequential diagram `F : ℕ ⥤ A` in an abelian category with countable coproducts and exact
sequential colimits (the countable case of AB5), this file constructs the resolution
`0 → S → P → F → 0` of `F` by partial coproducts and deduces that the telescope sequence
`0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → colim F → 0`, whose first map is `1 − shift`, is short exact.

## Main definitions

* `Stacks.MappingTelescope.Tel.P`: the diagram of partial coproducts `P_n = ⨁_{i ≤ n} F_i`.
* `Stacks.MappingTelescope.Tel.S`: the diagram of partial coproducts `S_n = ⨁_{i < n} F_i`.
* `Stacks.MappingTelescope.Tel.Dsc`: the short complex `S ⟶ P ⟶ F` of diagrams.

## Main results

* `Stacks.MappingTelescope.Tel.Dsc_shortExact`: the short complex `0 ⟶ S ⟶ P ⟶ F ⟶ 0` is short
  exact.
* `Stacks.MappingTelescope.telescope_general_hz`: the composite of the two telescope maps is zero.
* `Stacks.MappingTelescope.telescope_shortExact_general`: the telescope sequence
  `0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → colim F → 0` is short exact.
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.MappingTelescope

namespace Tel
universe vTel uTel
variable {A : Type uTel} [Category.{vTel} A] [Abelian A]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable (F : ℕ ⥤ A) [HasColimit F] [HasCoproduct (fun n => F.obj n)] [HasColimitsOfShape ℕ A]

/-! ### The diagram of partial coproducts `P_n = ⨁_{i ≤ n} F_i` -/

/-- The partial coproduct `P_n = ⨁_{i ≤ n} F_i`. -/
noncomputable def Pobj (n : ℕ) : A := ⨁ (fun (i : Fin (n+1)) => F.obj i.val)
/-- The inclusion `P_n ⟶ P_{n+1}` of partial coproducts. -/
noncomputable def Pmap (n : ℕ) : Pobj F n ⟶ Pobj F (n+1) :=
  biproduct.desc (fun (i : Fin (n+1)) =>
    biproduct.ι (fun (j : Fin (n+2)) => F.obj j.val) i.castSucc)
/-- The sequential diagram `n ↦ P_n` of partial coproducts, with the inclusions as transition
maps. -/
noncomputable def P : ℕ ⥤ A := Functor.ofSequence (Pmap F)
/-- The inclusion of the partial coproduct `P_n` into the coproduct `∐ₙ Fₙ`. -/
noncomputable def Pleg (n : ℕ) : Pobj F n ⟶ (∐ fun n => F.obj n) :=
  biproduct.desc (fun (i : Fin (n+1)) => Sigma.ι (fun n => F.obj n) i.val)

omit [HasColimit F] [HasColimitsOfShape ℕ A] in
/-- The inclusions `P_n ⟶ ∐ₙ Fₙ` are compatible with the inclusions `P_n ⟶ P_{n+1}`. -/
theorem Pmap_Pleg (n : ℕ) : Pmap F n ≫ Pleg F (n+1) = Pleg F n := by
  apply biproduct.hom_ext'
  intro i
  simp only [Pmap, Pleg, biproduct.ι_desc_assoc, biproduct.ι_desc, Fin.val_castSucc]

/-- Given maps `w_n : P_n ⟶ W`, the map `F_j ⟶ W` obtained by restricting `w_j` to the last
summand of `P_j`. -/
noncomputable def legComp {W : A} (w : ∀ n, Pobj F n ⟶ W) (j : ℕ) : F.obj j ⟶ W :=
  biproduct.ι (fun (i : Fin (j+1)) => F.obj i.val) (Fin.last j) ≫ w j

/-- A cocone over `Functor.ofSequence f` has legs compatible with the maps `f n`. -/
private theorem ofSequence_comp_cocone_app {C : Type*} [Category C] {X : ℕ → C}
    (f : ∀ n, X n ⟶ X (n + 1)) (s : Cocone (Functor.ofSequence f)) (n : ℕ) :
    f n ≫ s.ι.app (n + 1) = s.ι.app n := by
  simpa using s.ι.naturality (homOfLE (Nat.le_succ n))

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- For a cocone `s` over `P F`, the restriction of `s.ι.app n` to the summand `F_i` of `P_n` is
the restriction of `s.ι.app i` to the last summand of `P_i`. -/
theorem iota_app_legComp (s : Cocone (P F)) (n : ℕ) (i : Fin (n + 1)) :
    biproduct.ι (fun (k : Fin (n+1)) => F.obj k.val) i ≫ s.ι.app n
      = legComp F (fun m => s.ι.app m) i.val := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
      refine Fin.lastCases ?_ ?_ i
      · rfl
      · intro j
        have step : biproduct.ι (fun (k : Fin (n+2)) => F.obj k.val) j.castSucc ≫ s.ι.app (n+1)
            = biproduct.ι (fun (k : Fin (n+1)) => F.obj k.val) j ≫ s.ι.app n := by
          rw [← ofSequence_comp_cocone_app (Pmap F) s n, ← Category.assoc]; congr 1
          simp only [Pmap, biproduct.ι_desc]
        rw [step, ih j]; congr 1

/-- The cocone over `P F` with apex `∐ₙ Fₙ` whose legs are the inclusions `P_n ⟶ ∐ₙ Fₙ`. -/
noncomputable def Pcocone : Cocone (P F) where
  pt := ∐ fun n => F.obj n
  ι := NatTrans.ofSequence (F := P F) (G := (Functor.const ℕ).obj (∐ fun n => F.obj n))
        (fun n => Pleg F n) (by
          intro n
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [show (P F).map (homOfLE (Nat.le_succ n)) = Pmap F n from
              Functor.ofSequence_map_homOfLE_succ (Pmap F) n]
          exact Pmap_Pleg F n)

omit [HasColimit F] [HasColimitsOfShape ℕ A] in
/-- The legs of `Pcocone F` are the inclusions `P_n ⟶ ∐ₙ Fₙ`. -/
@[simp] theorem Pcocone_ι (n : ℕ) : (Pcocone F).ι.app n = Pleg F n := rfl

/-- The coproduct `∐ₙ Fₙ` is the colimit of the diagram `P F` of partial coproducts. -/
noncomputable def PisColimit : IsColimit (Pcocone F) where
  desc s := Sigma.desc (legComp F (fun m => s.ι.app m))
  fac s n := by
    rw [Pcocone_ι]
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc]
    simp only [Pleg, biproduct.ι_desc]
    rw [Sigma.ι_comp_desc]
    exact (iota_app_legComp F s n i).symm
  uniq s m hm := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    have h1 : biproduct.ι (fun (i : Fin (j+1)) => F.obj i.val) (Fin.last j) ≫ Pleg F j
        = Sigma.ι (fun n => F.obj n) j := by
      simp only [Pleg, biproduct.ι_desc]
      rfl
    rw [← h1, Category.assoc, show Pleg F j ≫ m = s.ι.app j by rw [← Pcocone_ι]; exact hm j]
    rfl

/-! ### The diagram of partial coproducts `S_n = ⨁_{i < n} F_i` -/

/-- The partial coproduct `S_n = ⨁_{i < n} F_i`; in particular `S_0` is zero. -/
noncomputable def Sobj (n : ℕ) : A := ⨁ (fun (i : Fin n) => F.obj i.val)
/-- The inclusion `S_n ⟶ S_{n+1}` of partial coproducts. -/
noncomputable def Smap (n : ℕ) : Sobj F n ⟶ Sobj F (n+1) :=
  biproduct.desc (fun (i : Fin n) => biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) i.castSucc)
/-- The sequential diagram `n ↦ S_n` of partial coproducts, with the inclusions as transition
maps. -/
noncomputable def S : ℕ ⥤ A := Functor.ofSequence (Smap F)
/-- The inclusion of the partial coproduct `S_n` into the coproduct `∐ₙ Fₙ`. -/
noncomputable def Sleg (n : ℕ) : Sobj F n ⟶ (∐ fun n => F.obj n) :=
  biproduct.desc (fun (i : Fin n) => Sigma.ι (fun n => F.obj n) i.val)

omit [HasColimit F] [HasColimitsOfShape ℕ A] in
/-- The inclusions `S_n ⟶ ∐ₙ Fₙ` are compatible with the inclusions `S_n ⟶ S_{n+1}`. -/
theorem Smap_Sleg (n : ℕ) : Smap F n ≫ Sleg F (n+1) = Sleg F n := by
  apply biproduct.hom_ext'
  intro i
  simp only [Smap, Sleg, biproduct.ι_desc_assoc, biproduct.ι_desc, Fin.val_castSucc]

/-- Given maps `w_n : S_n ⟶ W`, the map `F_j ⟶ W` obtained by restricting `w_{j+1}` to the last
summand of `S_{j+1}`. -/
noncomputable def SlegComp {W : A} (w : ∀ n, Sobj F n ⟶ W) (j : ℕ) : F.obj j ⟶ W :=
  biproduct.ι (fun (i : Fin (j+1)) => F.obj i.val) (Fin.last j) ≫ w (j+1)

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- For a cocone `s` over `S F`, the restriction of `s.ι.app n` to the summand `F_i` of `S_n` is
the restriction of `s.ι.app (i + 1)` to the last summand of `S_{i+1}`. -/
theorem iota_app_SlegComp (s : Cocone (S F)) (n : ℕ) (i : Fin n) :
    biproduct.ι (fun (k : Fin n) => F.obj k.val) i ≫ s.ι.app n
      = SlegComp F (fun m => s.ι.app m) i.val := by
  induction n with
  | zero => exact absurd i.isLt (by simp)
  | succ n ih =>
      refine Fin.lastCases ?_ ?_ i
      · rfl
      · intro j
        have step : biproduct.ι (fun (k : Fin (n+1)) => F.obj k.val) j.castSucc ≫ s.ι.app (n+1)
            = biproduct.ι (fun (k : Fin n) => F.obj k.val) j ≫ s.ι.app n := by
          rw [← ofSequence_comp_cocone_app (Smap F) s n, ← Category.assoc]; congr 1
          simp only [Smap, biproduct.ι_desc]
        rw [step, ih j]; congr 1

/-- The cocone over `S F` with apex `∐ₙ Fₙ` whose legs are the inclusions `S_n ⟶ ∐ₙ Fₙ`. -/
noncomputable def Scocone : Cocone (S F) where
  pt := ∐ fun n => F.obj n
  ι := NatTrans.ofSequence (F := S F) (G := (Functor.const ℕ).obj (∐ fun n => F.obj n))
        (fun n => Sleg F n) (by
          intro n
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [show (S F).map (homOfLE (Nat.le_succ n)) = Smap F n from
              Functor.ofSequence_map_homOfLE_succ (Smap F) n]
          exact Smap_Sleg F n)

omit [HasColimit F] [HasColimitsOfShape ℕ A] in
/-- The legs of `Scocone F` are the inclusions `S_n ⟶ ∐ₙ Fₙ`. -/
@[simp] theorem Scocone_ι (n : ℕ) : (Scocone F).ι.app n = Sleg F n := rfl

/-- The coproduct `∐ₙ Fₙ` is the colimit of the diagram `S F` of partial coproducts. -/
noncomputable def SisColimit : IsColimit (Scocone F) where
  desc s := Sigma.desc (SlegComp F (fun m => s.ι.app m))
  fac s n := by
    rw [Scocone_ι]
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc]
    simp only [Sleg, biproduct.ι_desc]
    rw [Sigma.ι_comp_desc]
    exact (iota_app_SlegComp F s n i).symm
  uniq s m hm := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    have h1 : biproduct.ι (fun (i : Fin (j+1)) => F.obj i.val) (Fin.last j) ≫ Sleg F (j+1)
        = Sigma.ι (fun n => F.obj n) j := by
      simp only [Sleg, biproduct.ι_desc]
      rfl
    rw [← h1, Category.assoc,
      show Sleg F (j+1) ≫ m = s.ι.app (j+1) by rw [← Scocone_ι]; exact hm (j+1)]
    rfl

/-! ### The map π : P ⟹ F -/

/-- The map `P_n ⟶ F_n` given on the summand `F_i` by the transition map `F_i ⟶ F_n`. -/
noncomputable def pimap (n : ℕ) : Pobj F n ⟶ F.obj n :=
  biproduct.desc (fun (i : Fin (n+1)) => F.map (homOfLE (Nat.le_of_lt_succ i.isLt)))

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The maps `P_n ⟶ F_n` commute with the transition maps of `P F` and of `F`. -/
theorem Pmap_pimap (n : ℕ) :
    Pmap F n ≫ pimap F (n+1) = pimap F n ≫ F.map (homOfLE (Nat.le_succ n)) := by
  apply biproduct.hom_ext'
  intro i
  simp only [Pmap, pimap, biproduct.ι_desc_assoc, biproduct.ι_desc, Fin.val_castSucc]
  rw [← F.map_comp]
  congr 1

/-- The natural transformation `π : P F ⟶ F` with components `pimap F n : P_n ⟶ F_n`. -/
noncomputable def pi : P F ⟶ F :=
  NatTrans.ofSequence (F := P F) (G := F) (fun n => pimap F n) (by
    intro n
    rw [show (P F).map (homOfLE (Nat.le_succ n)) = Pmap F n from
        Functor.ofSequence_map_homOfLE_succ (Pmap F) n]
    exact Pmap_pimap F n)

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The components of `π` are the maps `pimap F n : P_n ⟶ F_n`. -/
@[simp] theorem pi_app (n : ℕ) : (pi F).app n = pimap F n := rfl

/-! ### colim π = can -/

/-- The canonical map `∐ₙ Fₙ ⟶ colim F` induced by the colimit inclusions. -/
noncomputable def can : (∐ fun n => F.obj n) ⟶ colimit F :=
  Sigma.desc (fun n => colimit.ι F n)

omit [HasColimitsOfShape ℕ A] in
/-- The composite `P_n ⟶ ∐ₙ Fₙ ⟶ colim F` equals `P_n ⟶ F_n ⟶ colim F`. -/
theorem Pleg_can (n : ℕ) : Pleg F n ≫ can F = pimap F n ≫ colimit.ι F n := by
  apply biproduct.hom_ext'
  intro i
  simp only [Pleg, can, pimap, biproduct.ι_desc_assoc, Sigma.ι_comp_desc]
  rw [colimit.w F (homOfLE (Nat.le_of_lt_succ i.isLt))]

/-- The isomorphism `colim (P F) ≅ ∐ₙ Fₙ`. -/
noncomputable def ePiso : colimit (P F) ≅ (∐ fun n => F.obj n) :=
  colimit.isoColimitCocone ⟨Pcocone F, PisColimit F⟩

omit [HasColimit F] in
/-- The isomorphism `colim (P F) ≅ ∐ₙ Fₙ` restricts on `P_n` to the inclusion `P_n ⟶ ∐ₙ Fₙ`. -/
@[simp] theorem ePiso_ι (n : ℕ) : colimit.ι (P F) n ≫ (ePiso F).hom = Pleg F n := by
  simp only [ePiso]
  rw [colimit.isoColimitCocone_ι_hom]
  rfl

/-- Under `colim (P F) ≅ ∐ₙ Fₙ`, the canonical map `∐ₙ Fₙ ⟶ colim F` is `colim π`. -/
theorem colimMap_pi : (ePiso F).hom ≫ can F = colim.map (pi F) := by
  apply colimit.hom_ext
  intro n
  rw [← Category.assoc, ePiso_ι, Pleg_can, show colim.map (pi F) = colimMap (pi F) from rfl,
    ι_colimMap, pi_app]

/-! ### The map 𝒿 : S ⟹ P -/

/-- For `i < n`, the map `ι_i - ι_{i+1} ∘ (F_i ⟶ F_{i+1}) : F_i ⟶ P_n`. -/
noncomputable def jsummand (n : ℕ) (i : Fin n) : F.obj i.val ⟶ Pobj F n :=
  biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    - F.map (homOfLE (Nat.le_succ i.val)) ≫
        biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩

/-- The map `𝒿_n : S_n ⟶ P_n` whose restriction to the summand `F_i` is
`ι_i - ι_{i+1} ∘ (F_i ⟶ F_{i+1})`. -/
noncomputable def jmap (n : ℕ) : Sobj F n ⟶ Pobj F n :=
  biproduct.desc (fun (i : Fin n) => jsummand F n i)

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The maps `𝒿_n : S_n ⟶ P_n` commute with the transition maps of `S F` and of `P F`. -/
theorem Smap_jmap (n : ℕ) : Smap F n ≫ jmap F (n+1) = jmap F n ≫ Pmap F n := by
  apply biproduct.hom_ext'
  intro i
  simp only [Smap, jmap, biproduct.ι_desc_assoc, biproduct.ι_desc]
  simp only [jsummand, Pmap, Preadditive.sub_comp, Category.assoc, biproduct.ι_desc]
  congr 1

/-- The natural transformation `𝒿 : S F ⟶ P F` with components `jmap F n : S_n ⟶ P_n`. -/
noncomputable def jnt : S F ⟶ P F :=
  NatTrans.ofSequence (F := S F) (G := P F) (fun n => jmap F n) (by
    intro n
    rw [show (S F).map (homOfLE (Nat.le_succ n)) = Smap F n from
        Functor.ofSequence_map_homOfLE_succ (Smap F) n,
      show (P F).map (homOfLE (Nat.le_succ n)) = Pmap F n from
        Functor.ofSequence_map_homOfLE_succ (Pmap F) n]
    exact Smap_jmap F n)

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The components of `𝒿` are the maps `jmap F n : S_n ⟶ P_n`. -/
@[simp] theorem jnt_app (n : ℕ) : (jnt F).app n = jmap F n := rfl

/-! ### colim 𝒿 = tel -/

/-- The telescope map `1 - shift : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ`, equal to `ιₙ - ιₙ₊₁ ∘ (Fₙ ⟶ Fₙ₊₁)` on the
summand `Fₙ`. -/
noncomputable def tel : (∐ fun n => F.obj n) ⟶ (∐ fun n => F.obj n) :=
  Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
    - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n+1))

omit [HasColimit F] [HasColimitsOfShape ℕ A] in
/-- The composite `S_n ⟶ ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` through the telescope map equals
`S_n ⟶ P_n ⟶ ∐ₙ Fₙ`. -/
theorem Sleg_tel (n : ℕ) : Sleg F n ≫ tel F = jmap F n ≫ Pleg F n := by
  apply biproduct.hom_ext'
  intro i
  simp only [Sleg, jmap, tel, biproduct.ι_desc_assoc, Sigma.ι_comp_desc]
  simp only [jsummand, Preadditive.sub_comp, Category.assoc, Pleg, biproduct.ι_desc]

/-- The isomorphism `colim (S F) ≅ ∐ₙ Fₙ`. -/
noncomputable def eSiso : colimit (S F) ≅ (∐ fun n => F.obj n) :=
  colimit.isoColimitCocone ⟨Scocone F, SisColimit F⟩

omit [HasColimit F] in
/-- The isomorphism `colim (S F) ≅ ∐ₙ Fₙ` restricts on `S_n` to the inclusion `S_n ⟶ ∐ₙ Fₙ`. -/
@[simp] theorem eSiso_ι (n : ℕ) : colimit.ι (S F) n ≫ (eSiso F).hom = Sleg F n := by
  simp only [eSiso]
  rw [colimit.isoColimitCocone_ι_hom]
  rfl

omit [HasColimit F] in
/-- Under `colim (S F) ≅ ∐ₙ Fₙ` and `colim (P F) ≅ ∐ₙ Fₙ`, the telescope map is `colim 𝒿`. -/
theorem colimMap_j : (eSiso F).hom ≫ tel F = colim.map (jnt F) ≫ (ePiso F).hom := by
  apply colimit.hom_ext
  intro n
  rw [← Category.assoc, eSiso_ι, Sleg_tel, show colim.map (jnt F) = colimMap (jnt F) from rfl,
    ← Category.assoc, ι_colimMap, jnt_app, Category.assoc, ePiso_ι]

/-! ### The section σ and the retraction ρ -/

/-- The inclusion `σ_n : F_n ⟶ P_n` of the last summand. -/
noncomputable def sigmasec (n : ℕ) : F.obj n ⟶ Pobj F n :=
  biproduct.ι (fun (i : Fin (n+1)) => F.obj i.val) (Fin.last n)

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The inclusion `σ_n : F_n ⟶ P_n` is a section of `π_n : P_n ⟶ F_n`. -/
theorem sigmasec_pimap (n : ℕ) : sigmasec F n ≫ pimap F n = 𝟙 (F.obj n) := by
  simp only [sigmasec, pimap, biproduct.ι_desc]
  rw [show homOfLE (Nat.le_of_lt_succ (Fin.last n).isLt) = 𝟙 n from Subsingleton.elim _ _]
  simp

/-- The map `ρ_n : P_n ⟶ S_n` sending the summand `F_k` to `∑_{k ≤ i < n} ι_i ∘ (F_k ⟶ F_i)`. -/
noncomputable def rho (n : ℕ) : Pobj F n ⟶ Sobj F n :=
  biproduct.desc (fun (k : Fin (n+1)) =>
    ∑ i : Fin n, if h : k.val ≤ i.val
      then F.map (homOfLE h) ≫ biproduct.ι (fun (i : Fin n) => F.obj i.val) i
      else 0)

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The restriction of `ρ_n : P_n ⟶ S_n` to the summand `F_m` is
`∑_{m ≤ i < n} ι_i ∘ (F_m ⟶ F_i)`. -/
theorem iota_rho (n m : ℕ) (hm : m < n + 1) :
    biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨m, hm⟩ ≫ rho F n
      = ∑ i : Fin n, if h : m ≤ i.val
          then F.map (homOfLE h) ≫ biproduct.ι (fun (i : Fin n) => F.obj i.val) i
          else 0 := by
  simp only [rho, biproduct.ι_desc]

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The map `ρ_n : P_n ⟶ S_n` is a retraction of `𝒿_n : S_n ⟶ P_n`. -/
theorem jmap_rho (n : ℕ) : jmap F n ≫ rho F n = 𝟙 (Sobj F n) := by
  apply biproduct.hom_ext'
  intro i
  simp only [jmap, biproduct.ι_desc_assoc]
  show jsummand F n i ≫ rho F n = _
  simp only [jsummand, Preadditive.sub_comp, Category.assoc, iota_rho]
  rw [Preadditive.comp_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [dite_eq_left (le_refl i.val), dite_eq_right (by omega)]
    simp only [comp_zero, sub_zero]
    rw [show homOfLE (le_refl i.val) = 𝟙 i.val from Subsingleton.elim _ _, F.map_id,
      Category.id_comp]
    exact (Category.comp_id _).symm
  · intro j _ hji
    by_cases hij : i.val ≤ j.val
    · have hlt : i.val + 1 ≤ j.val :=
        (lt_of_le_of_ne hij fun h ↦ hji (Fin.ext h).symm : i.val < j.val)
      rw [dite_eq_left hij, dite_eq_left hlt, ← Category.assoc, ← F.map_comp,
        show homOfLE hij = (homOfLE (Nat.le_succ i.val) ≫ homOfLE hlt) from
          Subsingleton.elim _ _, sub_self]
    · rw [dite_eq_right hij, dite_eq_right (by omega), comp_zero, sub_zero]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

/-- For `k ≤ n`, the telescoping sum `∑_{k ≤ i < n} (g i - g (i + 1))` equals `g k - g n`. -/
theorem fin_telescope {M : Type*} [AddCommGroup M] (g : ℕ → M) (k n : ℕ) (h : k ≤ n) :
    (∑ i : Fin n, if k ≤ i.val then (g i.val - g (i.val+1)) else 0) = g k - g n := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if k ≤ m then (g m - g (m+1)) else 0) n,
    ← Finset.sum_filter,
    show (Finset.range n).filter (fun m => k ≤ m) = Finset.Ico k n from by
      ext m; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega,
    Finset.sum_Ico_eq_sum_range]
  have hh : ∀ t, g (k + t) - g (k + t + 1) = (fun t => g (k+t)) t - (fun t => g (k+t)) (t+1) := by
    intro t
    simp [add_assoc]
  simp_rw [hh]
  rw [Finset.sum_range_sub' (fun t => g (k+t)) (n-k)]
  simp [Nat.add_sub_cancel' h]

/-- For `k ≤ m ≤ n`, the map `ι_m ∘ (F_k ⟶ F_m) : F_k ⟶ P_n`, and zero otherwise. -/
noncomputable def telSummand (n k m : ℕ) : F.obj k ⟶ Pobj F n :=
  if h : k ≤ m ∧ m < n + 1
    then F.map (homOfLE h.left) ≫
      biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨m, h.right⟩
    else 0

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- For `k ≤ i < n`, the composite of `F_k ⟶ F_i` with `jsummand F n i` equals
`telSummand F n k i - telSummand F n k (i + 1)`. -/
theorem map_jsummand (n k : ℕ) (i : Fin n) (hk : k ≤ i.val) :
    F.map (homOfLE hk) ≫ jsummand F n i
      = telSummand F n k i.val - telSummand F n k (i.val + 1) := by
  have h1 : k ≤ i.val ∧ i.val < n + 1 := ⟨hk, Nat.lt_succ_of_lt i.isLt⟩
  have h2 : k ≤ i.val + 1 ∧ i.val + 1 < n + 1 := ⟨Nat.le_succ_of_le hk, Nat.succ_lt_succ i.isLt⟩
  rw [jsummand, Preadditive.comp_sub, telSummand, telSummand, dite_eq_left h1, dite_eq_left h2]
  have e1 : F.map (homOfLE hk) ≫
      biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      = F.map (homOfLE h1.left) ≫
        biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val, h1.right⟩ := rfl
  have e2 : F.map (homOfLE hk) ≫ (F.map (homOfLE (Nat.le_succ i.val)) ≫
      biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩)
      = F.map (homOfLE h2.left)
        ≫ biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val+1, h2.right⟩ := by
    rw [← Category.assoc, ← F.map_comp]; congr 1
  rw [e1, e2]

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The map `telSummand F n k k` is the inclusion of the summand `F_k` into `P_n`. -/
theorem telSummand_self (n k : ℕ) (hk : k < n + 1) :
    telSummand F n k k = biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨k, hk⟩ := by
  rw [telSummand, dite_eq_left ⟨le_refl k, hk⟩,
    show homOfLE (le_refl k) = 𝟙 k from Subsingleton.elim _ _, F.map_id, Category.id_comp]

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- On the summand `F_k` of `P_n`, the composite `ρ_n ≫ 𝒿_n` is `ι_k - ι_n ∘ (F_k ⟶ F_n)`. -/
theorem iota_rho_jmap (n : ℕ) (k : Fin (n + 1)) :
    biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) k ≫ rho F n ≫ jmap F n
      = biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) k
        - F.map (homOfLE (Nat.le_of_lt_succ k.isLt)) ≫
            biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) (Fin.last n) := by
  rw [show k = (⟨k.val, k.isLt⟩ : Fin (n+1)) from rfl, ← Category.assoc, iota_rho,
    Preadditive.sum_comp]
  have hterm : ∀ i : Fin n,
      ((if h : k.val ≤ i.val then
          F.map (homOfLE h) ≫ biproduct.ι (fun (i : Fin n) => F.obj i.val) i
        else 0) ≫ jmap F n)
        = if k.val ≤ i.val then
            telSummand F n k.val i.val - telSummand F n k.val (i.val+1)
          else 0 := by
    intro i
    by_cases hh : k.val ≤ i.val
    · rw [dite_eq_left hh, ite_eq_left hh, Category.assoc,
        show biproduct.ι (fun (i : Fin n) => F.obj i.val) i ≫ jmap F n = jsummand F n i from by
          rw [jmap, biproduct.ι_desc]]
      exact map_jsummand F n k.val i hh
    · rw [dite_eq_right hh, ite_eq_right hh, zero_comp]
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    fin_telescope (telSummand F n k.val) k.val n (Nat.le_of_lt_succ k.isLt),
    telSummand_self F n k.val k.isLt,
    show telSummand F n k.val n = F.map (homOfLE (Nat.le_of_lt_succ k.isLt)) ≫
        biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) (Fin.last n) from by
      rw [telSummand, dite_eq_left ⟨Nat.le_of_lt_succ k.isLt, Nat.lt_succ_self n⟩]; rfl]

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- On the summand `F_k` of `P_n`, the composite `π_n ≫ σ_n` is `ι_n ∘ (F_k ⟶ F_n)`. -/
theorem iota_pimap_sigmasec (n : ℕ) (k : Fin (n + 1)) :
    biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) k ≫ pimap F n ≫ sigmasec F n
      = F.map (homOfLE (Nat.le_of_lt_succ k.isLt)) ≫
          biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) (Fin.last n) := by
  rw [← Category.assoc, pimap, biproduct.ι_desc, sigmasec]

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The maps `ρ_n` and `σ_n` satisfy `ρ_n ≫ 𝒿_n + π_n ≫ σ_n = 𝟙 P_n`. -/
theorem rho_jmap_add_pimap_sigmasec (n : ℕ) :
    rho F n ≫ jmap F n + pimap F n ≫ sigmasec F n = 𝟙 (Pobj F n) := by
  apply biproduct.hom_ext'
  intro k
  rw [Preadditive.comp_add, iota_rho_jmap F n k, iota_pimap_sigmasec F n k]
  have hid : biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) k ≫ 𝟙 (Pobj F n)
      = biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) k := Category.comp_id _
  rw [hid]
  abel

/-! ### The short exact sequence of diagrams -/

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The composite `𝒿_n ≫ π_n : S_n ⟶ F_n` is zero. -/
theorem jmap_pimap (n : ℕ) : jmap F n ≫ pimap F n = 0 := by
  apply biproduct.hom_ext'
  intro i
  simp only [jmap, biproduct.ι_desc_assoc, comp_zero]
  show jsummand F n i ≫ pimap F n = 0
  rw [jsummand, Preadditive.sub_comp, Category.assoc,
    show (biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        ≫ pimap F n)
        = F.map (homOfLE (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.isLt)))
        from by rw [pimap, biproduct.ι_desc],
    show (biproduct.ι (fun (j : Fin (n+1)) => F.obj j.val) ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
        ≫ pimap F n)
        = F.map (homOfLE (Nat.le_of_lt_succ (Nat.succ_lt_succ i.isLt)))
        from by rw [pimap, biproduct.ι_desc],
    ← F.map_comp,
    show (homOfLE (Nat.le_succ i.val) ≫ homOfLE (Nat.le_of_lt_succ (Nat.succ_lt_succ i.isLt)))
        = homOfLE (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.isLt)) from Subsingleton.elim _ _,
    sub_self]

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The composite `𝒿 ≫ π : S F ⟶ F` is zero. -/
theorem jnt_pi : jnt F ≫ pi F = 0 := by
  ext n
  exact jmap_pimap F n

/-- The diagram short complex `D = (S → P → F)` in `ℕ ⥤ A`. -/
noncomputable def Dsc : ShortComplex (ℕ ⥤ A) := ShortComplex.mk (jnt F) (pi F) (jnt_pi F)

/-- The splitting of the short complex `S_n ⟶ P_n ⟶ F_n` given by `ρ_n` and `σ_n`. -/
noncomputable def compSplitting (n : ℕ) : ((Dsc F).map ((evaluation ℕ A).obj n)).Splitting where
  r := rho F n
  s := sigmasec F n
  f_r := jmap_rho F n
  s_g := sigmasec_pimap F n
  id := rho_jmap_add_pimap_sigmasec F n

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The short complex `S F ⟶ P F ⟶ F` in `ℕ ⥤ A` is exact. -/
theorem Dsc_exact : (Dsc F).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext n
  have hn : ((Dsc F).map ((evaluation ℕ A).obj n)).Exact := (compSplitting F n).exact
  rw [ShortComplex.exact_iff_isZero_homology] at hn
  have e := (Dsc F).mapHomologyIso ((evaluation ℕ A).obj n)
  exact (IsZero.of_iso hn e.symm).eq_of_src _ _

omit [HasColimit F] [HasCoproduct fun n ↦ F.obj n] [HasColimitsOfShape ℕ A] in
/-- The short complex `0 ⟶ S F ⟶ P F ⟶ F ⟶ 0` in `ℕ ⥤ A` is short exact. -/
theorem Dsc_shortExact : (Dsc F).ShortExact := by
  have : ∀ n, Mono ((jnt F).app n) := fun n ↦ (compSplitting F n).isSplitMono_f.mono
  have : ∀ n, Epi ((pi F).app n) := fun n ↦ (compSplitting F n).isSplitEpi_g.epi
  exact ShortComplex.ShortExact.mk (Dsc_exact F) (mono_f := NatTrans.mono_of_mono_app (jnt F))
    (epi_g := NatTrans.epi_of_epi_app (pi F))

/-! ### The telescope short exact sequence -/

/-- There is a short exact sequence `D` in `ℕ ⥤ A` whose image under `colim` is isomorphic to
the telescope short complex `∐ₙ Fₙ ⟶ ∐ₙ Fₙ ⟶ colim F`. -/
theorem diagram_SES
    (hz : (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n + 1)))
        ≫ Sigma.desc (fun n => colimit.ι F n) = 0) :
    ∃ (D : ShortComplex (ℕ ⥤ A)) (_ : D.ShortExact),
      Nonempty (D.map (colim : (ℕ ⥤ A) ⥤ A) ≅
        ShortComplex.mk (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
            - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n+1)))
          (Sigma.desc (fun n => colimit.ι F n)) hz) := by
  refine ⟨Dsc F, Dsc_shortExact F, ⟨?_⟩⟩
  refine ShortComplex.isoMk (eSiso F) (ePiso F) (Iso.refl (colimit F)) ?_ ?_
  · change (eSiso F).hom ≫ _ = colim.map (jnt F) ≫ (ePiso F).hom
    exact colimMap_j F
  · change (ePiso F).hom ≫ _ = colim.map (pi F) ≫ 𝟙 _
    rw [Category.comp_id]
    exact colimMap_pi F

end Tel

/-- The composite of the telescope map `1 - shift` with the canonical map `∐ₙ Fₙ ⟶ colim F` is
zero. -/
theorem telescope_general_hz {A : Type*} [Category A] [Abelian A]
    (F : ℕ ⥤ A) [HasColimit F] [HasCoproduct (fun n => F.obj n)] :
    (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n+1)))
        ≫ Sigma.desc (fun n => colimit.ι F n) = 0 := by
  apply Sigma.hom_ext
  intro n
  rw [Sigma.ι_comp_desc_assoc, comp_zero, Preadditive.sub_comp, Category.assoc,
    Sigma.ι_comp_desc, Sigma.ι_comp_desc, colimit.w F (homOfLE n.le_succ), sub_self]

/-- **The mapping-telescope short exact sequence.**
If `A` has exact sequential colimits, the telescope sequence
`0 ⟶ ∐ₙ Fₙ ⟶ ∐ₙ Fₙ ⟶ colim F ⟶ 0`, whose first map is `1 - shift` and whose second map is
induced by the colimit inclusions, is short exact. -/
theorem telescope_shortExact_general {A : Type*} [Category A] [Abelian A]
    (F : ℕ ⥤ A) [HasColimit F] [HasCoproduct (fun n => F.obj n)]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    (hz : (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n + 1)))
        ≫ Sigma.desc (fun n => colimit.ι F n) = 0) :
    (ShortComplex.mk (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n+1)))
        (Sigma.desc (fun n => colimit.ι F n)) hz).ShortExact := by
  have : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A) :=
    (inferInstance : HasExactColimitsOfShape ℕ A).preservesFiniteLimits
  have : PreservesColimitsOfSize.{0,0} (colim : (ℕ ⥤ A) ⥤ A) :=
    (colimConstAdj (J := ℕ) (C := A)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (colim : (ℕ ⥤ A) ⥤ A) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  obtain ⟨D, hD, ⟨e⟩⟩ := Tel.diagram_SES F hz
  exact ShortComplex.shortExact_of_iso e (hD.map_of_exact _)

/-- If `A` has exact sequential colimits, the telescope map `1 - shift : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` is a
monomorphism. -/
theorem telescope_general_mono {A : Type*} [Category A] [Abelian A]
    (F : ℕ ⥤ A) [HasColimit F] [HasCoproduct (fun n => F.obj n)]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] :
    Mono (Sigma.desc (fun n => Sigma.ι (fun n => F.obj n) n
        - F.map (homOfLE n.le_succ) ≫ Sigma.ι (fun n => F.obj n) (n+1))) :=
  (telescope_shortExact_general F (telescope_general_hz F)).mono_f

end Stacks.MappingTelescope
