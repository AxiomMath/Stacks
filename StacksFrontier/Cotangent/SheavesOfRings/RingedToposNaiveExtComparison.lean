module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.Deformation.SquareZero.ExtBaseChange
public import StacksFrontier.Deformation.SquareZero.Obstruction
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphismsExt

/-!
# `Ext¹` out of the cotangent complex and out of the naive cotangent complex of a ringed topos

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `G` a sheaf of
`O_C`-modules. The canonical map `L_f ⟶ NL_f` of [Stacks Project, Tag 08V2] identifies `NL_f`
with the truncation `τ_{≥ -1} L_f`, and `G[1]` lies in degrees `≥ -1`, so maps into it only see
that truncation:

`Ext¹_{O_C}(NL_f, G) = Ext¹_{O_C}(L_f, G)`.

This is the identification through which the proof of [Stacks Project, Tag 08V5], clause (2),
reads the statements of Deformation Theory, phrased with the naive cotangent complex, as
statements about the cotangent complex.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.naiveCotangentExt`: `Ext^i_{O_C}(NL_f, G)`.
* `AlgebraicGeometry.RingedToposHom.naiveExtOneEquiv`:
  `Ext¹_{O_C}(NL_f, G) ≃+ Ext¹_{O_C}(L_f, G)`.

## Main results

* `AlgebraicGeometry.RingedToposHom.isIso_truncGE_map_Q_canonicalNaiveComparison`: the map
  `L_f ⟶ NL_f` becomes an isomorphism after `τ_{≥ -1}`.
* `AlgebraicGeometry.RingedToposHom.naiveExtOneEquiv_apply`: the identification is
  precomposition with that map.

## References

* [Stacks Project, Tag 08V2](https://stacks.math.columbia.edu/tag/08V2)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y) (G : Sheaf.targetModules.{u, v, w} X.J X.O)
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- The naive cotangent complex `NL_f = NL_{O_C/f⁻¹O_D}` of [Stacks Project, Tag 08TW],
regarded in the derived category of sheaves of `O_C`-modules. -/
noncomputable abbrev naiveCotangentComplexDerived :
    DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O) :=
  DerivedCategory.Q.obj
    (Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} X.J _ X.O
      f.fSharpInverseImage)

/-- `Ext^i_{O_C}(NL_f, G)`, formed in the derived category of sheaves of `O_C`-modules. -/
noncomputable abbrev naiveCotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext f.naiveCotangentComplexDerived (singleDerived G) i

/-- **Stacks 08V2** in the derived category: the canonical map `L_f ⟶ NL_f` becomes an
isomorphism after the truncation `τ_{≥ -1}`, being an isomorphism on the cohomology sheaves of
every degree `≥ -1`. -/
theorem isIso_truncGE_map_Q_canonicalNaiveComparison :
    IsIso (((DerivedCategory.TStructure.t
        (C := Sheaf.targetModules.{u, v, w} X.J X.O)).truncGE (-1)).map
      (DerivedCategory.Q.map f.canonicalNaiveComparison)) := by
  rw [Stacks.DerivedTruncation.isIso_truncGE_map_iff_forall_isIso_homologyMap]
  intro i hi
  refine (NatIso.isIso_map_iff
    (DerivedCategory.homologyFunctorFactors (Sheaf.targetModules.{u, v, w} X.J X.O) i) _).2 ?_
  exact f.canonicalNaiveComparison_isIso_homologyMap i hi

/-- `G[0]⟦1⟧` lies in degrees `≥ -1`. -/
instance isGE_singleDerived_shift_one :
    (DerivedCategory.TStructure.t (C := Sheaf.targetModules.{u, v, w} X.J X.O)).IsGE
      ((singleDerived G)⟦(1 : ℤ)⟧) (-1) :=
  DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by decide)

/-- **`Ext¹_{O_C}(NL_f, G) = Ext¹_{O_C}(L_f, G)`**: maps into `G[1]` only see the truncation
`τ_{≥ -1}`, and `τ_{≥ -1} L_f = NL_f` by [Stacks Project, Tag 08V2]. -/
noncomputable def naiveExtOneEquiv : f.naiveCotangentExt G 1 ≃+ f.cotangentExt G 1 :=
  haveI := f.isIso_truncGE_map_Q_canonicalNaiveComparison
  (Stacks.Deformation.truncGEHomAddEquiv
      (DerivedCategory.TStructure.t (C := Sheaf.targetModules.{u, v, w} X.J X.O)) (-1)
      f.naiveCotangentComplexDerived ((singleDerived G)⟦(1 : ℤ)⟧)).symm.trans
    ((Stacks.Deformation.extOneSourceIso (asIso
      (((DerivedCategory.TStructure.t
        (C := Sheaf.targetModules.{u, v, w} X.J X.O)).truncGE (-1)).map
        (DerivedCategory.Q.map f.canonicalNaiveComparison))).symm).trans
    (Stacks.Deformation.truncGEHomAddEquiv
      (DerivedCategory.TStructure.t (C := Sheaf.targetModules.{u, v, w} X.J X.O)) (-1)
      f.cotangentComplexDerived ((singleDerived G)⟦(1 : ℤ)⟧)))

/-- The identification `Ext¹_{O_C}(NL_f, G) = Ext¹_{O_C}(L_f, G)` is precomposition with the
canonical map `L_f ⟶ NL_f`. -/
theorem naiveExtOneEquiv_apply (x : f.naiveCotangentExt G 1) :
    f.naiveExtOneEquiv G x = DerivedCategory.Q.map f.canonicalNaiveComparison ≫ x := by
  have := f.isIso_truncGE_map_Q_canonicalNaiveComparison
  let t := DerivedCategory.TStructure.t (C := Sheaf.targetModules.{u, v, w} X.J X.O)
  let e := Stacks.Deformation.truncGEHomAddEquiv t (-1) f.naiveCotangentComplexDerived
    ((singleDerived G)⟦(1 : ℤ)⟧)
  have hy : (t.truncGEπ (-1)).app _ ≫ e.symm x = x := e.apply_symm_apply x
  have key : f.naiveExtOneEquiv G x =
      (t.truncGEπ (-1)).app f.cotangentComplexDerived ≫
        (t.truncGE (-1)).map (DerivedCategory.Q.map f.canonicalNaiveComparison) ≫ e.symm x :=
    rfl
  rw [key, ← Category.assoc, t.truncGEπ_naturality, Category.assoc, hy]

end AlgebraicGeometry.RingedToposHom

end
