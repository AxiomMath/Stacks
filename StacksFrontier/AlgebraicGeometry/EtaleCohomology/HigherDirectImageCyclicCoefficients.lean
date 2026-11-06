module

public import StacksFrontier.Algebra.Category.Grp.AdditiveFunctorFiniteGroups
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldConstantSheaves
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# Higher direct images with coefficients annihilated by `n` are detected by `ℤ/dℤ`, `d ∣ n`

Let `h : Y ⟶ X` be quasi-compact and quasi-separated, let `e : Y ⟶ T` be any morphism and let
`n` be an integer. If `R^r h_* e⁻¹(ℤ/dℤ) = 0` for every `d ∣ n`, the sheaves `ℤ/dℤ` being
constant on `T`, then `R^r h_* e⁻¹(M) = 0` for the constant sheaf on every abelian group `M`
annihilated by `n`.

When `T` is the spectrum of a separably closed field every abelian sheaf on `T` is constant
(`Stacks.EtaleCohomology.isIso_constantSheafToSheaf_of_isSepClosed`), so the conclusion holds for
every abelian sheaf on `T` annihilated by `n`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_pullback_constantSheaf_of_forall_zmod` — the
  statement for constant sheaves on an arbitrary `T`.
* `Stacks.EtaleCohomology.isZero_rightDerived_pullback_of_forall_zmod` — the statement for every
  abelian sheaf annihilated by `n` on the spectrum of a separably closed field.

## References

* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Subgroups

variable (M : AddCommGrpCat.{u + 1})

/-- The finitely generated subgroups of an abelian group, ordered by inclusion. -/
abbrev FGAddSubgroup : Type (u + 1) := {S : AddSubgroup M // S.FG}

/-- The finitely generated subgroups of an abelian group are directed: two of them are contained
in their join. -/
instance : IsDirected (FGAddSubgroup M) (· ≤ ·) where
  directed S T := ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩

/-- The trivial subgroup is finitely generated. -/
instance : Nonempty (FGAddSubgroup M) := ⟨⟨⊥, AddSubgroup.FG.bot⟩⟩

/-- The diagram of finitely generated subgroups of an abelian group and their inclusions. -/
def fgAddSubgroupDiagram : FGAddSubgroup M ⥤ AddCommGrpCat.{u + 1} where
  obj S := AddCommGrpCat.of S.1
  map f := AddCommGrpCat.ofHom (AddSubgroup.inclusion (leOfHom f))

/-- The cocone of inclusions of the finitely generated subgroups into the group. -/
def fgAddSubgroupCocone : Cocone (fgAddSubgroupDiagram M) where
  pt := M
  ι := { app S := AddCommGrpCat.ofHom S.1.subtype }

/-- An abelian group is the filtered colimit of its finitely generated subgroups. -/
def isColimitFGAddSubgroupCocone : IsColimit (fgAddSubgroupCocone M) := by
  have : ReflectsColimitsOfShape (FGAddSubgroup M) (forget AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget AddCommGrpCat.{u + 1})
    (Types.FilteredColimit.isColimitOf _ _ (fun x ↦ ?_) (fun i j xi xj hij ↦ ?_))
  · let y : M := x
    refine ⟨⟨AddSubgroup.zmultiples y, (AddSubgroup.fg_iff _).2
      ⟨{y}, (AddSubgroup.zmultiples_eq_closure y).symm, Set.finite_singleton y⟩⟩,
      ⟨y, AddSubgroup.mem_zmultiples y⟩, rfl⟩
  · refine ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩,
      homOfLE (show i.1 ≤ i.1 ⊔ j.1 from le_sup_left),
      homOfLE (show j.1 ≤ i.1 ⊔ j.1 from le_sup_right), ?_⟩
    exact Subtype.ext hij

end Subgroups

/-- **Constant coefficients annihilated by `n` are detected by `ℤ/dℤ`, `d ∣ n`.** Let
`h : Y ⟶ X` be quasi-compact and quasi-separated and `e : Y ⟶ T` any morphism. If
`R^r h_* e⁻¹(ℤ/dℤ) = 0` for every `d ∣ n`, then `R^r h_* e⁻¹(M) = 0` for every abelian group
`M` annihilated by `n`, `M` and `ℤ/dℤ` standing for the constant sheaves on `T`. -/
theorem isZero_rightDerived_pullback_constantSheaf_of_forall_zmod {X Y T : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (e : Y ⟶ T) (r : ℕ) (n : ℤ)
    (hd : ∀ d : ℕ, (d : ℤ) ∣ n → IsZero (((smallEtalePushforwardAb h).rightDerived r).obj
      ((smallEtalePullbackAb e).obj ((constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))))))
    (M : AddCommGrpCat.{u + 1}) (hM : ∀ x : M, n • x = 0) :
    IsZero (((smallEtalePushforwardAb h).rightDerived r).obj
      ((smallEtalePullbackAb e).obj
        ((constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj M))) := by
  let L := constantSheaf (smallEtaleTopology T) Ab.{u + 1} ⋙ smallEtalePullbackAb e
  let adj := constantSheafAdj (smallEtaleTopology T) Ab.{u + 1}
    (IsTerminal.ofUniqueHom toEtaleMkId fun _ a ↦ toEtaleMkId_unique a)
  have : (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{u + 1, u + 1} (constantSheaf (smallEtaleTopology T) Ab.{u + 1}) :=
    adj.leftAdjoint_preservesColimits
  have : L.Additive :=
    inferInstanceAs (constantSheaf (smallEtaleTopology T) Ab.{u + 1} ⋙
      smallEtalePullbackAb e).Additive
  have : PreservesColimitsOfSize.{u + 1, u + 1} (smallEtalePullbackAb e) :=
    (smallEtaleAdjunctionAb e).leftAdjoint_preservesColimits
  have hL : IsColimit (L.mapCocone (fgAddSubgroupCocone M)) :=
    isColimitOfPreserves L (isColimitFGAddSubgroupCocone M)
  let G := fgAddSubgroupDiagram M ⋙ L
  have hG (S) : IsZero (((smallEtalePushforwardAb h).rightDerived r).obj (G.obj S)) := by
    have : AddGroup.FG S.1 := (AddGroup.fg_iff_addSubgroup_fg S.1).2 S.2
    exact AddCommGrpCat.isZero_obj_of_fg_of_zsmul_eq_zero
      (L ⋙ (smallEtalePushforwardAb h).rightDerived r) n hd (AddCommGrpCat.of S.1)
      fun x ↦ Subtype.ext (hM x)
  exact (isZero_rightDerived_smallEtalePushforwardAb_colimit h r G hG).of_iso
    (((smallEtalePushforwardAb h).rightDerived r).mapIso
      ((colimit.isColimit G).coconePointUniqueUpToIso hL)).symm

/-- **Over a separably closed field, coefficients annihilated by `n` are detected by `ℤ/dℤ`,
`d ∣ n`.** Let `k` be separably closed, `h : Y ⟶ X` quasi-compact and quasi-separated and
`e : Y ⟶ Spec k`. If `R^r h_* e⁻¹(ℤ/dℤ) = 0` for every `d ∣ n`, then `R^r h_* e⁻¹F = 0` for every
abelian sheaf `F` on the small étale site of `Spec k` annihilated by `n`. -/
theorem isZero_rightDerived_pullback_of_forall_zmod (k : Type u) [Field k] [IsSepClosed k]
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (e : Y ⟶ Spec (.of k))
    (r : ℕ) (n : ℤ)
    (hd : ∀ d : ℕ, (d : ℤ) ∣ n → IsZero (((smallEtalePushforwardAb h).rightDerived r).obj
      ((smallEtalePullbackAb e).obj
        ((constantSheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))))))
    (F : Sheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1})
    (hF : ∀ (U : (Spec (.of k)).Etale) (x : F.obj.obj (op U)), n • x = 0) :
    IsZero (((smallEtalePushforwardAb h).rightDerived r).obj ((smallEtalePullbackAb e).obj F)) := by
  have := isIso_constantSheafToSheaf_of_isSepClosed k F
  exact (isZero_rightDerived_pullback_constantSheaf_of_forall_zmod h e r n hd _
    (hF _)).of_iso (((smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived r).mapIso
      (asIso (constantSheafToSheaf F))).symm)

end Stacks.EtaleCohomology

end
