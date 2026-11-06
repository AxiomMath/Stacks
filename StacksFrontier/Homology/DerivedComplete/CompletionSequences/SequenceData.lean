module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.SurjectiveTowerDifference
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.AdicWeakSerreClass
public import StacksFrontier.Homology.DerivedComplete.CountableMilnorTower
public import StacksFrontier.Homology.DerivedComplete.PrincipalTorsionTower
public import StacksFrontier.Homology.Injectives.FilteredComplex.MappingCone
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Principal completion sequences: the data

The inverse systems of `f`-power torsion and quotients, the fixed mapping-cocone model of the
derived inverse limit, the comparison structures for completion, shifts and canonical
truncations, and the structure `PrincipalCompletionSequences` recording the two sequences
of Stacks 0BKG together with the uniqueness of their normalized arrows.
-/

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v w x

namespace CompletionSequences

attribute [local instance] HasDerivedCategory.standard

/-- The quotient map from `M / f^(n+2)M` to `M / f^(n+1)M`. -/
public def powerQuotientTransition (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    cokernel (powerMultiplication A M (f ^ (n + 2))) ⟶
      cokernel (powerMultiplication A M (f ^ (n + 1))) :=
  cokernel.desc _ (cokernel.π _) (by
    rw [show powerMultiplication A M (f ^ (n + 2)) =
        powerMultiplication A M f ≫ powerMultiplication A M (f ^ (n + 1)) by
      ext x
      simp [powerMultiplication, pow_succ', smul_smul], Category.assoc,
      cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
public lemma π_powerQuotientTransition (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    cokernel.π (powerMultiplication A M (f ^ (n + 2))) ≫
        powerQuotientTransition A M f n =
      cokernel.π (powerMultiplication A M (f ^ (n + 1))) := by
  apply cokernel.π_desc

/-- The inverse system `M / f^(n+1)M` with its canonical quotient transition maps. -/
public def powerQuotientSystem (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (f : A) : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  Functor.ofOpSequence
    (X := fun n ↦ cokernel (powerMultiplication A M (f ^ (n + 1))))
    (powerQuotientTransition A M f)

@[simp]
public lemma powerQuotientSystem_obj (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    (powerQuotientSystem A M f).obj ⟨n⟩ =
      cokernel (powerMultiplication A M (f ^ (n + 1))) := rfl

@[simp]
public lemma powerQuotientSystem_map_succ (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (f : A) (n : ℕ) :
    (powerQuotientSystem A M f).map (homOfLE (Nat.le_succ n)).op =
      powerQuotientTransition A M f n := by
  apply Functor.ofOpSequence_map_homOfLE_succ

/-- The `f`-adic Tate module `T_f(M) = lim M[f^(n+1)]`. -/
@[sga "1 XI 2.1" "more general", sga "7 I 6.1" "partial"]
public abbrev adicTateModule (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (f : A) : ModuleCat.{v} A :=
  limit (powerTorsionSystem A M f)

variable (A : Type u) [CommRing A]

/-- The product of the complexes in an inverse system. -/
public abbrev complexProduct (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) :=
  ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩

/-- The map `1 - shift` on the product of a complex inverse system. -/
public def complexDifference (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) :
    complexProduct A E ⟶ complexProduct A E :=
  Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op

/-- The compatible cone inclusions, assembled into a map to the product. -/
public noncomputable def principalComplexUnit (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    C ⟶ complexProduct A (principalComplexSystem A f C) :=
  Pi.lift (f := fun n : ℕ ↦ (principalComplexSystem A f C).obj ⟨n⟩)
    fun n ↦ CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C)

/-- Each component of the map to the product is the cone inclusion. -/
@[reassoc (attr := simp)]
public lemma principalComplexUnit_π (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    principalComplexUnit A f C ≫
        Pi.π (fun n : ℕ ↦ (principalComplexSystem A f C).obj ⟨n⟩) n =
      CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C) := by
  apply Pi.lift_comp_π

set_option backward.isDefEq.respectTransparency false in
/-- The compatible cone inclusions are killed by `1 - shift`. -/
public lemma principalComplexUnit_difference (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    principalComplexUnit A f C ≫ complexDifference A (principalComplexSystem A f C) = 0 := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, complexDifference, Pi.lift_comp_π, comp_sub, ← Category.assoc,
    principalComplexUnit_π, principalComplexUnit_π, zero_comp]
  rw [show (principalComplexSystem A f C).map (homOfLE (Nat.le_succ n)).op = _ from
    Functor.ofOpSequence_map_homOfLE_succ _ n]
  rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_desc,
    Category.id_comp, sub_self]

/-- The canonical map into the mapping cocone, with zero homotopy component. -/
public noncomputable def principalCompletionUnit (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    C ⟶ CochainComplex.mappingCocone
      (complexDifference A (principalComplexSystem A f C)) :=
  CochainComplex.mappingCocone.lift _ (principalComplexUnit A f C) 0 (by
    simp [principalComplexUnit_difference])

/-- The chain-level unit has exactly the specified compatible cone inclusions as projections. -/
@[reassoc (attr := simp)]
public lemma principalCompletionUnit_fst (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    principalCompletionUnit A f C ≫
        CochainComplex.mappingCocone.fst (complexDifference A (principalComplexSystem A f C)) =
      principalComplexUnit A f C := by
  apply CochainComplex.mappingCocone.lift_fst

/-- The fixed Milnor triangle: the image of the mapping-cocone triangle for `1 - shift`. -/
public abbrev milnorTriangle (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) :
    Triangle (DerivedCategory (ModuleCat.{v} A)) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle (complexDifference A E))

/-- The fixed Milnor triangle is distinguished. -/
public theorem milnorTriangle_distinguished
    (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) :
    milnorTriangle A E ∈ distTriang (DerivedCategory (ModuleCat.{v} A)) :=
  DerivedCategory.mappingCocone_triangle_distinguished _

/-- The product of the terms of a module inverse system. -/
public abbrev moduleProduct (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) := ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩

/-- The map `1 - shift` on the product of a module inverse system. -/
public def moduleDifference (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) : moduleProduct A E ⟶ moduleProduct A E :=
  Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op

/-- The cokernel model of the first derived inverse limit. -/
public abbrev firstDerivedLimit (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) := cokernel (moduleDifference A E)

/-- The fixed mapping-cocone model of the derived inverse limit of modules. -/
public abbrev moduleDerivedLimit (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) :=
  (milnorTriangle A (E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0)).obj₁

/-- A module placed in degree zero as a complex. -/
public abbrev moduleComplex (M : ModuleCat.{v} A) :=
  (CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj M

/-- The principal Koszul tower of a module. -/
public abbrev moduleTower (f : A) (M : ModuleCat.{v} A) :=
  principalComplexSystem A f (moduleComplex A M)

/-- The fixed triangle for multiplication by a power of `f` on a module. -/
public abbrev moduleConeTriangle (f : A) (M : ModuleCat.{v} A) (n : ℕ) :=
  DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 (moduleComplex A M)))

/-- Cohomology in the independent module universe. -/
public abbrev homology (p : ℤ) := homologyFunctor (ModuleCat.{v} A) p

/-- A module placed in the specified degree of the derived category. -/
public abbrev single (p : ℤ) := DerivedCategory.singleFunctor (ModuleCat.{v} A) p

/-- The canonical cohomology identification for a module in a single degree. -/
public abbrev singleHomology (p : ℤ) (M : ModuleCat.{v} A) :=
  (singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) p).app M

/-- The standard identification of the degree-one cohomology of the fixed module
Milnor object with the cokernel of `1 - shift`, including its connecting-map normalization. -/
public structure FirstDerivedLimitComparison (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) where
  productIso : (homology A 0).obj (DerivedCategory.Q.obj
    (complexProduct A (E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0))) ≅ moduleProduct A E
  productIso_π (n : ℕ) :
    productIso.hom ≫ Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n =
      (homology A 0).map (DerivedCategory.Q.map
        (Pi.π (fun n : ℕ ↦ (moduleComplex A (E.obj ⟨n⟩))) n)) ≫
          (singleHomology A 0 (E.obj ⟨n⟩)).hom
  iso : (homology A 1).obj (moduleDerivedLimit A E) ≅ firstDerivedLimit A E
  connecting_iso :
    productIso.hom ≫ cokernel.π (moduleDifference A E) ≫ iso.inv =
      (homology A 0).homologySequenceδ
        (milnorTriangle A (E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0)) 0 1 (by omega)

variable (f : A)
variable (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
variable (η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F)

/-- The comparison is normalized by the actual chain-level map into the mapping cocone,
not just by its projections in the derived category. -/
public structure CompletionComparison where
  iso (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    F.obj (DerivedCategory.Q.obj C) ≅ (milnorTriangle A (principalComplexSystem A f C)).obj₁
  unit_iso (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    η.app (DerivedCategory.Q.obj C) ≫ (iso C).hom =
      DerivedCategory.Q.map (principalCompletionUnit A f C)

/-- The module sequence with its maps normalized by the fixed mapping-cocone triangle. -/
public structure ModuleCompletionSequence (c : CompletionComparison A f F η)
    (M : ModuleCat.{v} A) where
  torsionIso : moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A (-1) ≅ powerTorsionSystem A M f
  quotientIso : moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A 0 ≅ powerQuotientSystem A M f
  torsionIso_ι (n : ℕ) :
    torsionIso.hom.app ⟨n⟩ ≫ kernel.ι (powerMultiplication A M (f ^ (n + 1))) =
      (homology A 0).homologySequenceδ (moduleConeTriangle A f M n) (-1) 0 (by omega) ≫
        (singleHomology A 0 M).hom
  π_quotientIso (n : ℕ) :
    (singleHomology A 0 M).inv ≫
        (homology A 0).map (moduleConeTriangle A f M n).mor₂ ≫ quotientIso.hom.app ⟨n⟩ =
      cokernel.π (powerMultiplication A M (f ^ (n + 1)))
  productIso : (homology A (-1)).obj (milnorTriangle A (moduleTower A f M)).obj₃ ≅
    moduleProduct A (powerTorsionSystem A M f)
  productIso_π (n : ℕ) :
    productIso.hom ≫ Pi.π (fun n : ℕ ↦ (powerTorsionSystem A M f).obj ⟨n⟩) n =
      (homology A (-1)).map (DerivedCategory.Q.map
        (Pi.π (fun n : ℕ ↦ (moduleTower A f M).obj ⟨n⟩) n)) ≫ torsionIso.hom.app ⟨n⟩
  tateIso : (homology A (-1)).obj (F.obj ((single A 0).obj M)) ≅ adicTateModule A M f
  tateIso_π (n : ℕ) :
    tateIso.hom ≫ limit.π (powerTorsionSystem A M f) ⟨n⟩ =
      (homology A (-1)).map ((c.iso (moduleComplex A M)).hom ≫
        (milnorTriangle A (moduleTower A f M)).mor₁ ≫ DerivedCategory.Q.map
          (Pi.π (fun n : ℕ ↦ (moduleTower A f M).obj ⟨n⟩) n)) ≫ torsionIso.hom.app ⟨n⟩
  inclusion : firstDerivedLimit A (powerTorsionSystem A M f) ⟶
    (homology A 0).obj (F.obj ((single A 0).obj M))
  projection : (homology A 0).obj (F.obj ((single A 0).obj M)) ⟶ limit (powerQuotientSystem A M f)
  connecting_inclusion :
    productIso.hom ≫ cokernel.π (moduleDifference A (powerTorsionSystem A M f)) ≫ inclusion =
      (homology A 0).homologySequenceδ (milnorTriangle A (moduleTower A f M)) (-1) 0 (by omega) ≫
        (homology A 0).map (c.iso (moduleComplex A M)).inv
  projection_π (n : ℕ) :
    projection ≫ limit.π (powerQuotientSystem A M f) ⟨n⟩ =
      (homology A 0).map ((c.iso (moduleComplex A M)).hom ≫
        (milnorTriangle A (moduleTower A f M)).mor₁ ≫ DerivedCategory.Q.map
          (Pi.π (fun n : ℕ ↦ (moduleTower A f M).obj ⟨n⟩) n)) ≫ quotientIso.hom.app ⟨n⟩
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- Completion commutes with shifts via the unique isomorphism respecting its unit. -/
public structure CompletionShift where
  iso (X : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) : F.obj (X⟦n⟧) ≅ (F.obj X)⟦n⟧
  unit_iso (X : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) :
    η.app (X⟦n⟧) ≫ (iso X n).hom = (η.app X)⟦n⟧'

variable {A F η}

/-- The completion-shift comparison for a module in an arbitrary degree. -/
public def CompletionShift.singleIso (s : CompletionShift A F η)
    (M : ModuleCat.{v} A) (n k i : ℤ) (h : -n + k = i) :
    (homology A k).obj (F.obj ((single A n).obj M)) ≅
      (homology A i).obj (F.obj ((single A 0).obj M)) :=
  (homology A k).mapIso
    (F.mapIso (((DerivedCategory.singleFunctors (ModuleCat.{v} A)).shiftIso
      (-n) n 0 (by omega)).app M).symm ≪≫ s.iso ((single A 0).obj M) (-n)) ≪≫
        ((homology A 0).shiftIso (-n) k i h).app _

section ConeShift

open CochainComplex CochainComplex.HomComplex

variable {C : Type w} [Category.{x} C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The cone shift scales the `-fst` cocycle defining the connecting map. -/
public theorem coneShiftIso_hom_neg_fst (n i : ℤ) :
    (mappingCone.shiftIso φ n).hom.f i ≫
        (-(mappingCone.fst (φ⟦n⟧')).1.v i (i + 1) rfl) =
      n.negOnePow • (-(mappingCone.fst φ).1.v (i + n) (i + 1 + n) (by omega)) := by
  dsimp [mappingCone.shiftIso]
  simp [mappingCone.lift_f_fst_v, Cocycle.coe_units_smul, Cocycle.shift_coe,
    Cochain.units_smul_v, Cochain.shift_v', smul_neg]

/-- The cone shift preserves the inclusion used by the completion unit. -/
public theorem coneShiftIso_hom_inr (n : ℤ) :
    (mappingCone.inr φ)⟦n⟧' ≫ (mappingCone.shiftIso φ n).hom =
      mappingCone.inr (φ⟦n⟧') := by
  ext i : 1
  dsimp
  apply (mappingCone.ext_to_iff _ _ (i + 1) rfl _ _).2
  constructor
  · simp [mappingCone.shiftIso, Cocycle.coe_units_smul, Cocycle.shift_coe,
      Cochain.units_smul_v, Cochain.shift_v']
  · simp [mappingCone.shiftIso, Cochain.shift_v']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The connecting morphism acquires precisely the shift sign. -/
public theorem coneShiftIso_hom_mor₃ (n : ℤ) :
    (mappingCone.shiftIso φ n).hom ≫ (mappingCone.triangle (φ⟦n⟧')).mor₃ =
      n.negOnePow • ((mappingCone.triangle φ).mor₃⟦n⟧' ≫
        (shiftFunctorComm (CochainComplex C ℤ) 1 n).hom.app K) := by
  simpa [mappingCone.shiftTriangleIso] using (mappingCone.shiftTriangleIso φ n).hom.comm₃.symm

/-- The shift used by the upper truncation comparison gives `(p + 1).negOnePow`. -/
public theorem coneShiftIso_hom_mor₃_neg_succ (p : ℤ) :
    (mappingCone.shiftIso φ (-(p + 1))).hom ≫
        (mappingCone.triangle (φ⟦-(p + 1)⟧')).mor₃ =
      (p + 1).negOnePow • ((mappingCone.triangle φ).mor₃⟦-(p + 1)⟧' ≫
        (shiftFunctorComm (CochainComplex C ℤ) 1 (-(p + 1))).hom.app K) := by
  rw [coneShiftIso_hom_mor₃, Int.negOnePow_neg]

end ConeShift

variable (A F)
public abbrev truncLE (p : ℤ) := (DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).truncLE p
public abbrev truncGE (p : ℤ) := (DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).truncGE p
public abbrev truncIn (p : ℤ) := (DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).truncLEι p
public abbrev truncOut (p : ℤ) := (DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).truncGEπ p

/-- Endpoint comparisons for the canonical truncation triangle. The two pure-degree
isomorphisms are normalized on homology; the maps that completion makes invertible are explicit. -/
public structure TruncationIdentifications (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) where
  lower : (truncGE A p).obj ((truncLE A p).obj K) ≅ (single A p).obj ((homology A p).obj K)
  lower_homology :
    (homology A p).map ((truncOut A p).app ((truncLE A p).obj K)) ≫
        (homology A p).map lower.hom ≫ (singleHomology A p ((homology A p).obj K)).hom =
      (homology A p).map ((truncIn A p).app K)
  upper : (truncLE A (p + 1)).obj ((truncGE A (p + 1)).obj K) ≅
    (single A (p + 1)).obj ((homology A (p + 1)).obj K)
  upper_homology :
    (homology A (p + 1)).map upper.hom ≫
        (singleHomology A (p + 1) ((homology A (p + 1)).obj K)).hom ≫
          (homology A (p + 1)).map ((truncOut A (p + 1)).app K) =
      (homology A (p + 1)).map ((truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K))
  lower_isIso : IsIso ((homology A p).map
    (F.map ((truncOut A p).app ((truncLE A p).obj K) ≫ lower.hom)))
  upper_isIso : IsIso ((homology A p).map
    (F.map (upper.inv ≫ (truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K))))

attribute [instance] TruncationIdentifications.lower_isIso TruncationIdentifications.upper_isIso
variable {A F}

/-- The lower edge map, induced by completion of `τ≤p K → K`. -/
public def TruncationIdentifications.inclusion {K : DerivedCategory (ModuleCat.{v} A)} {p : ℤ}
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η) :
    (homology A 0).obj (F.obj ((single A 0).obj ((homology A p).obj K))) ⟶
      (homology A p).obj (F.obj K) :=
  (s.singleIso ((homology A p).obj K) p p 0 (by omega)).inv ≫
    inv ((homology A p).map (F.map ((truncOut A p).app ((truncLE A p).obj K) ≫ t.lower.hom))) ≫
      (homology A p).map (F.map ((truncIn A p).app K))

/-- The upper edge map, induced by completion of `K → τ≥p+1 K`, with the cone sign.

`CompletionShift.singleIso` uses the unit-preserving shift by `-(p + 1)`. Mathlib's
`mappingCone.shiftIso` multiplies `fst` by `(-(p + 1)).negOnePow = (p + 1).negOnePow`,
whereas `mappingCone.triangle.mor₃` is induced by `-fst`. The factor below compensates
for this shift when using the module `tateIso`, whose connecting-map convention is fixed.
It is `1` at `p = -1` and `-1` at `p = 0`. -/
public def TruncationIdentifications.projection {K : DerivedCategory (ModuleCat.{v} A)} {p : ℤ}
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η)
    (e : (homology A (-1)).obj (F.obj ((single A 0).obj ((homology A (p + 1)).obj K))) ≅
      adicTateModule A ((homology A (p + 1)).obj K) f) :
    (homology A p).obj (F.obj K) ⟶ adicTateModule A ((homology A (p + 1)).obj K) f :=
  (p + 1).negOnePow •
    ((homology A p).map (F.map ((truncOut A (p + 1)).app K)) ≫
      inv ((homology A p).map (F.map (t.upper.inv ≫
        (truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K)))) ≫
          (s.singleIso ((homology A (p + 1)).obj K) (p + 1) p (-1) (by omega)).hom ≫ e.hom)

/-- In even shifted degree, the cone normalization leaves the original composite unchanged. -/
public theorem TruncationIdentifications.projection_of_even
    {K : DerivedCategory (ModuleCat.{v} A)} {p : ℤ}
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η)
    (e : (homology A (-1)).obj (F.obj ((single A 0).obj ((homology A (p + 1)).obj K))) ≅
      adicTateModule A ((homology A (p + 1)).obj K) f) (hp : Even (p + 1)) :
    t.projection f s e =
      (homology A p).map (F.map ((truncOut A (p + 1)).app K)) ≫
        inv ((homology A p).map (F.map (t.upper.inv ≫
          (truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K)))) ≫
            (s.singleIso ((homology A (p + 1)).obj K) (p + 1) p (-1) (by omega)).hom ≫
              e.hom := by
  rw [TruncationIdentifications.projection, Int.negOnePow_even _ hp, one_smul]

/-- In odd shifted degree, the cone normalization negates the original composite. -/
public theorem TruncationIdentifications.projection_of_odd
    {K : DerivedCategory (ModuleCat.{v} A)} {p : ℤ}
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η)
    (e : (homology A (-1)).obj (F.obj ((single A 0).obj ((homology A (p + 1)).obj K))) ≅
      adicTateModule A ((homology A (p + 1)).obj K) f) (hp : Odd (p + 1)) :
    t.projection f s e =
      -((homology A p).map (F.map ((truncOut A (p + 1)).app K)) ≫
        inv ((homology A p).map (F.map (t.upper.inv ≫
          (truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K)))) ≫
            (s.singleIso ((homology A (p + 1)).obj K) (p + 1) p (-1) (by omega)).hom ≫
              e.hom) := by
  rw [TruncationIdentifications.projection, Int.negOnePow_odd _ hp, Units.neg_smul, one_smul]

/-- Undoing the endpoint comparisons recovers the completed truncation map with its
cone-shift factor. This is the right-hand analogue of `inclusion_truncIn`. -/
public theorem TruncationIdentifications.projection_truncOut
    {K : DerivedCategory (ModuleCat.{v} A)} {p : ℤ}
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η)
    (e : (homology A (-1)).obj (F.obj ((single A 0).obj ((homology A (p + 1)).obj K))) ≅
      adicTateModule A ((homology A (p + 1)).obj K) f) :
    t.projection f s e ≫ e.inv ≫
        (s.singleIso ((homology A (p + 1)).obj K) (p + 1) p (-1) (by omega)).inv ≫
          (homology A p).map (F.map (t.upper.inv ≫
            (truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K))) =
      (p + 1).negOnePow • (homology A p).map (F.map ((truncOut A (p + 1)).app K)) := by
  simp [TruncationIdentifications.projection, Linear.units_smul_comp]

/-- Multiplying the right arrow by the cone-shift sign preserves short exactness. -/
public theorem shortExact_negOnePow_smul_right
    {C : Type w} [Category.{x} C] [Abelian C] {X Y Z : C}
    (i : X ⟶ Y) (q : Y ⟶ Z) (h : i ≫ q = 0)
    (n : ℤ) (hs : (ShortComplex.mk i q h).ShortExact) :
    (ShortComplex.mk i (n.negOnePow • q)
      (by rw [Linear.comp_units_smul, h, smul_zero])).ShortExact := by
  apply ShortComplex.shortExact_of_iso _ hs
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (n.negOnePow • Iso.refl _)
    (by simp) (by simp)

variable (A F η)
/-- The two sequences of 0BKG, with all comparisons and arrows tied to the completion unit,
the fixed mapping-cocone model of the derived limit, and the canonical truncation maps. -/
public structure PrincipalCompletionSequences where
  comparison : CompletionComparison A f F η
  shift : CompletionShift A F η
  moduleSequence (M : ModuleCat.{v} A) : ModuleCompletionSequence A f F η comparison M
  truncation (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) : TruncationIdentifications A F K p
  truncation_zero (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    (truncation K p).inclusion shift ≫
      (truncation K p).projection f shift (moduleSequence ((homology A (p + 1)).obj K)).tateIso = 0
  truncation_shortExact (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    (ShortComplex.mk ((truncation K p).inclusion shift)
      ((truncation K p).projection f shift (moduleSequence ((homology A (p + 1)).obj K)).tateIso)
      (truncation_zero K p)).ShortExact

variable {A f F η}
/-- The module projection extends the ordinary completion unit. This follows from the
chain-level unit and the cone quotient normalization. -/
public theorem ModuleCompletionSequence.unit_projection
    {c : CompletionComparison A f F η} {M : ModuleCat.{v} A}
    (s : ModuleCompletionSequence A f F η c M) (n : ℕ) :
    (singleHomology A 0 M).inv ≫ (homology A 0).map (η.app ((single A 0).obj M)) ≫
        s.projection ≫ limit.π (powerQuotientSystem A M f) ⟨n⟩ =
      cokernel.π (powerMultiplication A M (f ^ (n + 1))) := by
  rw [s.projection_π, ← Functor.map_comp_assoc]
  have h : η.app ((single A 0).obj M) ≫
      ((c.iso (moduleComplex A M)).hom ≫
        (milnorTriangle A (moduleTower A f M)).mor₁ ≫ DerivedCategory.Q.map
          (Pi.π (fun n : ℕ ↦ (moduleTower A f M).obj ⟨n⟩) n)) =
      (moduleConeTriangle A f M n).mor₂ := by
    have hη : η.app ((single A 0).obj M) ≫ (c.iso (moduleComplex A M)).hom =
        DerivedCategory.Q.map (principalCompletionUnit A f (moduleComplex A M)) :=
      c.unit_iso (moduleComplex A M)
    rw [← Category.assoc, hη]
    show DerivedCategory.Q.map (principalCompletionUnit A f (moduleComplex A M)) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) ≫
        DerivedCategory.Q.map _ = DerivedCategory.Q.map _
    rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      principalCompletionUnit_fst, principalComplexUnit_π]
    rfl
  rw [h]
  exact s.π_quotientIso n

/-- The connecting equation determines the left arrow uniquely. -/
public theorem ModuleCompletionSequence.inclusion_ext
    {c : CompletionComparison A f F η} {M : ModuleCat.{v} A}
    (s : ModuleCompletionSequence A f F η c M)
    (i : firstDerivedLimit A (powerTorsionSystem A M f) ⟶
      (homology A 0).obj (F.obj ((single A 0).obj M)))
    (h : s.productIso.hom ≫ cokernel.π (moduleDifference A (powerTorsionSystem A M f)) ≫ i =
      (homology A 0).homologySequenceδ (milnorTriangle A (moduleTower A f M)) (-1) 0 (by omega) ≫
        (homology A 0).map (c.iso (moduleComplex A M)).inv) : i = s.inclusion := by
  apply (cancel_epi (cokernel.π (moduleDifference A (powerTorsionSystem A M f)))).1
  apply (cancel_epi s.productIso.hom).1
  exact h.trans s.connecting_inclusion.symm

/-- The projection equations determine the right arrow uniquely. -/
public theorem ModuleCompletionSequence.projection_ext
    {c : CompletionComparison A f F η} {M : ModuleCat.{v} A}
    (s : ModuleCompletionSequence A f F η c M)
    (q : (homology A 0).obj (F.obj ((single A 0).obj M)) ⟶ limit (powerQuotientSystem A M f))
    (h : ∀ n : ℕ, q ≫ limit.π (powerQuotientSystem A M f) ⟨n⟩ =
      (homology A 0).map ((c.iso (moduleComplex A M)).hom ≫
        (milnorTriangle A (moduleTower A f M)).mor₁ ≫ DerivedCategory.Q.map
          (Pi.π (fun n : ℕ ↦ (moduleTower A f M).obj ⟨n⟩) n)) ≫ s.quotientIso.hom.app ⟨n⟩) :
    q = s.projection := by
  apply limit.hom_ext
  intro n
  exact (h n.unop).trans (s.projection_π n.unop).symm

/-- Transporting the explicitly normalized left term recovers the original `H¹(R lim)`
form of the module short exact sequence. -/
public theorem ModuleCompletionSequence.shortExact_derivedLimit
    {c : CompletionComparison A f F η} {M : ModuleCat.{v} A}
    (s : ModuleCompletionSequence A f F η c M)
    (e : FirstDerivedLimitComparison A (powerTorsionSystem A M f)) :
    (ShortComplex.mk (e.iso.hom ≫ s.inclusion) s.projection
      (by rw [Category.assoc, s.zero, comp_zero])).ShortExact := by
  apply ShortComplex.shortExact_of_iso _ s.shortExact
  exact ShortComplex.isoMk e.iso.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The injection is induced by `τ≤p K → K`, under the normalized endpoint comparison. -/
public theorem TruncationIdentifications.inclusion_truncIn
    {K : DerivedCategory (ModuleCat.{v} A)} {p : ℤ}
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η) :
    (homology A p).map (F.map ((truncOut A p).app ((truncLE A p).obj K) ≫ t.lower.hom)) ≫
        (s.singleIso ((homology A p).obj K) p p 0 (by omega)).hom ≫ t.inclusion s =
      (homology A p).map (F.map ((truncIn A p).app K)) := by
  simp [TruncationIdentifications.inclusion]

set_option backward.isDefEq.respectTransparency false in
private lemma moduleDerivedLimit_isDerivedLimit
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) :
    IsDerivedLimit (E ⋙ single A 0) (moduleDerivedLimit A E) := by
  let X : ℕ → CochainComplex (ModuleCat.{v} A) ℤ := fun n => moduleComplex A (E.obj ⟨n⟩)
  let c := piComparison DerivedCategory.Q X
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{v} A) (I := ℕ)
  have hc : IsIso c := inferInstance
  let : IsIso c := hc
  let T := milnorTriangle A (E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0)
  let d := Pi.lift fun n : ℕ =>
    Pi.π (fun n : ℕ => DerivedCategory.Q.obj (X n)) n -
      Pi.π (fun n : ℕ => DerivedCategory.Q.obj (X n)) (n + 1) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).map
          (E.map (homOfLE (Nat.le_succ n)).op))
  have hd : T.mor₂ ≫ c = c ≫ d := by
    show DerivedCategory.Q.map (complexDifference A
      (E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0)) ≫ c = c ≫ d
    apply Pi.hom_ext
    intro n
    dsimp [d, c]
    rw [Category.assoc, piComparison_comp_π, Category.assoc, Pi.lift_comp_π,
      comp_sub, piComparison_comp_π, piComparison_comp_π_assoc]
    rw [← Functor.map_comp, complexDifference]
    simp [X]
  let T' := Triangle.mk (T.mor₁ ≫ c) d (inv c ≫ T.mor₃)
  let ec : _ ≅ _ := @asIso _ _ _ _ c hc
  refine ⟨T.mor₁ ≫ c, inv c ≫ T.mor₃, ?_⟩
  apply isomorphic_distinguished T (milnorTriangle_distinguished A _) T'
  exact (Triangle.isoMk T T' (Iso.refl _) ec ec
    (by change T.mor₁ ≫ c = 𝟙 _ ≫ (T.mor₁ ≫ c); simp) (by exact hd)
    (by
      dsimp [T', ec]
      show (milnorTriangle A (E ⋙ CochainComplex.singleFunctor
        (ModuleCat.{v} A) 0)).mor₃ ≫ (shiftFunctor _ 1).map (𝟙 _) =
        c ≫ inv c ≫ (milnorTriangle A (E ⋙ CochainComplex.singleFunctor
          (ModuleCat.{v} A) 0)).mor₃
      simp)).symm

end CompletionSequences
end

end
