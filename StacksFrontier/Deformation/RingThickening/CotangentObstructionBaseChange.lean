module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality
public import StacksFrontier.Cotangent.DerivedBaseChange
public import StacksFrontier.Cotangent.NaiveComparisonIsIso
public import StacksFrontier.Deformation.SquareZero.Problem
public import StacksFrontier.Homology.TwoTermComplex.BaseChange

/-!
# The comparison `L_{A/A'} → NL_{A/A'}` after base change to `B`

Let `A' → A → B` be ring maps. The map `L_{A/A'} → NL_{A/A'}` of Tag 08RB becomes an isomorphism
after the truncation `τ_{≥ -1}`, and so does its termwise base change
`L_{A/A'} ⊗_A B → NL_{A/A'} ⊗_A B`: the derived base change is right t-exact, the terms of
`L_{A/A'}` are projective, so its termwise base change is its derived base change, and the
termwise base change of `NL_{A/A'}`, whose degree-zero term is flat, computes `τ_{≥ -1}` of its
derived base change (Tag 0G9G). This is what identifies `Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N)` with
`Ext¹_B(NL_{A/A'} ⊗_A B, N)` in the proof of Tag 08SP, part (1).

## Main results

* `Stacks.isIso_truncGE_map_map_of_isIso_truncGE_map`: a triangulated functor of derived
  categories preserving each `D^{≤ n}` preserves morphisms which are isomorphisms after `τ_{≥ n}`.
* `isIso_truncGE_map_Q_extendScalars_cotangentComplexToNaive`, in the namespace
  `Stacks.Deformation.SquareZeroExtensionProblem`: the termwise base change of
  `L_{A/A'} → NL_{A/A'}` is an isomorphism after `τ_{≥ -1}`.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
* [Stacks Project, Tag 0G9G](https://stacks.math.columbia.edu/tag/0G9G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u u₄

namespace Stacks

/-- If `a ≫ b = c ≫ d` with `a` and `b` isomorphisms, then `c ≫ d` is an isomorphism. -/
private theorem isIso_comp_of_comp_eq_comp {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X}
    {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (w : a ≫ b = c ≫ d) [IsIso a] [IsIso b] :
    IsIso (c ≫ d) := by
  rw [← w]
  infer_instance

/-- **A right t-exact triangulated functor preserves `τ_{≥ n}`-isomorphisms.** If `G` carries
each `D^{≤ m}` into `D^{≤ m}` and `τ_{≥ n} f` is an isomorphism, so is `τ_{≥ n} (G f)`: the
truncation triangle `τ_{< n} X → X → τ_{≥ n} X` goes to a triangle whose first vertex lies in
degrees `< n`, so `G X → G (τ_{≥ n} X)` is an isomorphism after `τ_{≥ n}`. -/
theorem isIso_truncGE_map_map_of_isIso_truncGE_map {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (hG : ∀ (X : DerivedCategory C) (m : ℤ), X.IsLE m → (G.obj X).IsLE m)
    {X Y : DerivedCategory C} (f : X ⟶ Y) (n : ℤ)
    [IsIso ((DerivedCategory.TStructure.t.truncGE n).map f)] :
    IsIso ((DerivedCategory.TStructure.t.truncGE n).map (G.map f)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let t' := DerivedCategory.TStructure.t (C := D)
  have hπ : ∀ Z : DerivedCategory C,
      IsIso ((t'.truncGE n).map (G.map ((t.truncGEπ n).app Z))) := fun Z => by
    have hT := G.map_distinguished _ (t.triangleLTGE_distinguished n Z)
    have hle : t'.IsLE (G.mapTriangle.obj ((t.triangleLTGE n).obj Z)).obj₁ (n - 1) :=
      hG _ (n - 1) (inferInstance : t.IsLE ((t.truncLT n).obj Z) (n - 1))
    exact t'.isIso₂_truncGE_map_of_isLE _ hT (n - 1) n (by omega) hle
  have hnat : (t'.truncGE n).map (G.map ((t.truncGEπ n).app X)) ≫
      (t'.truncGE n).map (G.map ((t.truncGE n).map f)) =
      (t'.truncGE n).map (G.map f) ≫ (t'.truncGE n).map (G.map ((t.truncGEπ n).app Y)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      t.truncGEπ_naturality]
  have := hπ X
  have := isIso_comp_of_comp_eq_comp hnat
  exact IsIso.of_isIso_comp_right _ ((t'.truncGE n).map (G.map ((t.truncGEπ n).app Y)))

/-- **A t-exact functor of abelian categories preserves `D^{≤ m}`** on derived categories. -/
theorem mapDerivedCategory_isLE {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) (hX : X.IsLE m) : (F.mapDerivedCategory.obj X).IsLE m := by
  obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X m
  have : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero (K.isZero_of_isStrictlyLE m i hi)
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsLE m :=
    inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (X := DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (Y := F.mapDerivedCategory.obj X)
    ((F.mapDerivedCategory.mapIso e) ≪≫ F.mapDerivedCategoryFactors.app K).symm m

end Stacks

namespace Stacks.Cotangent

attribute [local instance high] HasDerivedCategory.standard

/-- **The map `L_{B/A} → NL_{B/A}` is an isomorphism after `τ_{≥ -1}`** (Tag 08RB): it is an
isomorphism on cohomology in degrees `-1` and `0`, and both complexes vanish in positive
degrees. -/
theorem isIso_truncGE_map_Q_cotangentComplexToNaive (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A) :
    IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{u} B)).truncGE (-1)).map
      (DerivedCategory.Q.map (cotangentComplexToNaive.{u, u} A B))) := by
  rw [Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap]
  intro i hi
  refine (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i) _).2
    ?_
  change IsIso (HomologicalComplex.homologyMap (cotangentComplexToNaive.{u, u} A B) i)
  by_cases h : i = -1 ∨ i = 0
  · exact isIso_homologyMap_cotangentComplexToNaive A B i h
  have hsrc : IsZero ((CommAlgCat.cotangentComplex.{u, u} A B).homology i) :=
    (HomologicalComplex.ExactAt.of_isZero
      (CommAlgCat.cotangentComplex_isZero_pos A B i (by omega))).isZero_homology
  have htgt : IsZero ((Algebra.Extension.naiveComplex
      (CommAlgCat.naiveExtension.{u, u} A B)).homology i) :=
    (HomologicalComplex.ExactAt.of_isZero (Algebra.Extension.isZero_naiveComplex_X _ i
      (by omega) (by omega))).isZero_homology
  exact ⟨⟨htgt.to_ _, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

end Stacks.Cotangent

namespace Stacks.Deformation.SquareZeroExtensionProblem

attribute [local instance high] HasDerivedCategory.standard

variable (S : SquareZeroExtensionProblem.{u, u, u, u₄})

/-- Extension of scalars along `A → B`. -/
noncomputable abbrev baseChangeFunctor : ModuleCat.{u} S.A ⥤ ModuleCat.{u} S.B :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap S.A S.B)

/-- **The termwise base change of `L_{A/A'} → NL_{A/A'}` is an isomorphism after `τ_{≥ -1}`.**
The derived base change is right t-exact, the terms of `L_{A/A'}` are projective, and the termwise
base change of `NL_{A/A'}`, whose degree-zero term is flat, computes `τ_{≥ -1}` of its derived base
change (Tag 0G9G). -/
theorem isIso_truncGE_map_Q_extendScalars_cotangentComplexToNaive :
    IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGE (-1)).map
      (DerivedCategory.Q.map ((S.baseChangeFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A))))) := by
  let : S.baseChangeFunctor.IsLeftAdjoint :=
    ModuleCat.instIsLeftAdjointExtendScalars.{u, u, u} (algebraMap S.A S.B)
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap S.A S.B)
  let := D.additive
  let := D.commShift
  let := D.isTriangulated
  have := D.isLeftDerived
  have : HasExactColimitsOfShape ℕ (ModuleCat.{u} S.A) :=
    TwoTermComplex.hasExactColimitsOfShape_nat_moduleCat
  have : HasExactColimitsOfShape ℕ (ModuleCat.{u} S.B) :=
    TwoTermComplex.hasExactColimitsOfShape_nat_moduleCat
  let L := CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A)
  let NL := Algebra.Extension.naiveComplex (CommAlgCat.naiveExtension.{u, u} S.A'
    (CommAlgCat.of S.A' S.A))
  have := Cotangent.isIso_truncGE_map_Q_cotangentComplexToNaive S.A' (CommAlgCat.of S.A' S.A)
  have hDc : IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGE (-1)).map
      (D.functor.map (DerivedCategory.Q.map
        (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A))))) :=
    isIso_truncGE_map_map_of_isIso_truncGE_map D.functor
      (fun X m hX => @D.maps_t_le X m hX)
      (DerivedCategory.Q.map (Cotangent.cotangentComplexToNaive.{u, u} S.A'
        (CommAlgCat.of S.A' S.A))) (-1)
  have hL : IsIso (D.comparison.app L) := by
    have : L.IsStrictlyLE 0 := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => CommAlgCat.cotangentComplex_isZero_pos _ _ i hi
    have : ∀ i, Projective (L.X i) :=
      CommAlgCat.projective_cotangentComplex_X'.{u, u} S.A' (CommAlgCat.of S.A' S.A)
    exact D.comparison_isIso_of_projective L 0
  have hNL : IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGE
      (-1)).map (D.comparison.app NL)) := by
    have hX : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (NL.X i) :=
      Algebra.Extension.isZero_naiveComplex_X _
    have hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).obj
          (DerivedCategory.Q.obj NL)) :=
      fun i h₁ h₀ => (HomologicalComplex.ExactAt.of_isZero (hX i h₁ h₀)).isZero_homology.of_iso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S.A) i).app _)
    have hflat : Module.Flat S.A (NL.X 0) :=
      Module.Flat.of_linearEquiv (Algebra.Extension.naiveComplexXZeroIso _).toLinearEquiv
    obtain ⟨f, hf, hfiso⟩ := @TwoTermComplex.twoTermBaseChange_iso_truncGE.{u, u, u}
      S.A S.B _ _ (algebraMap S.A S.B) (DerivedCategory.Q.obj NL) NL (Iso.refl _)
      hK hX hflat D.functor D.comparison D.isLeftDerived
    have he : ((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGEπ (-1)).app
          _ ≫ f = D.comparison.app NL := by
      rw [hf]
      exact (congrArg (· ≫ D.comparison.app NL) (D.functor.map_id _)).trans
        (Category.id_comp _)
    have := (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} S.B)).isIso_truncGE_map_truncGEπ_app (-1) (-1) le_rfl
      (D.functor.obj (DerivedCategory.Q.obj NL))
    have key : IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGE
        (-1)).map (((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGEπ
          (-1)).app _ ≫ f)) := by
      rw [Functor.map_comp]
      infer_instance
    rwa [he] at key
  have hnat := congrArg ((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGE
    (-1)).map (D.comparison.naturality
      (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A)))
  simp only [Functor.map_comp, Functor.comp_map] at hnat
  have hcomp := isIso_comp_of_comp_eq_comp hnat
  have hL' : IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{u} S.B)).truncGE
      (-1)).map (D.comparison.app L)) := Functor.map_isIso _ _
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hL' hcomp

end Stacks.Deformation.SquareZeroExtensionProblem

end
