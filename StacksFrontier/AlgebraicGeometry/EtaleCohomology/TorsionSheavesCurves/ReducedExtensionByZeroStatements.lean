module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsAllUniverses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothConstantCurveStatements

/-!
# Lemma 0A3Q: statements (1) -- (8) of Situation 0A52 for `j_! 𝐙/ℓ𝐙` on a reduced `X`

Let `k` be an algebraically closed field and `X` a separated scheme of finite type and dimension
at most one over `k` (Situation 0A52), and assume `X` is reduced. Let `j : U → X` be an open
immersion, `ℓ` a prime and `F = j_! 𝐙/ℓ𝐙`. Lemma 0A3Q of the source says that statements
(1) -- (8) of Situation 0A52 hold for `F`.

## Main results

* `Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_prime`: **Lemma
  0A3Q**, at every coefficient universe and every `Ext` universe.
* `Stacks.Torsion.torsionSheafProperty_of_nsmul_id_eq_zero`: an abelian sheaf killed by a positive
  integer is torsion.

## Implementation notes

**The proof.** The source passes to the normalization of `X` and uses Lemmas 03SG, 0A5D and 0GJA;
in the library that argument is
`Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_isReduced`, which takes
Lemma 0A5B on smooth curves as its hypothesis `hbase` and is stated at the coefficients
`AddCommGrpCat.{u + 1}` with `Ext` in universe `u + 1`. Here the statement is proved at every
coefficient universe `max (u + 1) v` and every `Ext` universe `w`, as Lemma 0A5B is
(`Stacks.EtaleCohomology.curveStatements_constantSheaf_of_smooth`): `j_! 𝐙/ℓ𝐙` is killed by `ℓ`,
hence a torsion sheaf, and the reduction theorem
`Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_max` gives the eight statements for
every torsion sheaf, its only input being Lemma 0A5B for `𝐙/ℓ𝐙` on smooth curves, which is
`Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_prime`. The reducedness of `X`
is therefore not used; the statement keeps it because the source does.

**The coefficients.** The constant sheaf is taken with value any abelian group `E` cyclic of order
`ℓ` (`Nonempty (E ≃+ ZMod ℓ)`), as in Lemma 0A5B; `ULift (ZMod ℓ)` is one such group.

## References

* [Stacks Project, Tag 0A3Q](https://stacks.math.columbia.edu/tag/0A3Q)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe w v u

namespace Stacks.Torsion

/-- **An abelian sheaf killed by a positive integer is torsion**: every section is annihilated by
that integer, on the maximal sieve. -/
theorem torsionSheafProperty_of_nsmul_id_eq_zero {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {F : Sheaf J AddCommGrpCat.{w}} {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) : torsionSheafProperty J F := by
  intro U x
  refine ⟨⊤, J.top_mem U, fun V f _ ↦ ⟨n, hn, ?_⟩⟩
  generalize F.obj.map f.op x = y
  have h := congrArg (fun g : F ⟶ F ↦ ((sheafToPresheaf J _).map g).app (Opposite.op V) y) hF
  simp only [Functor.map_nsmul, Functor.map_zero, NatTrans.app_nsmul, NatTrans.app_zero] at h
  simpa using h

end Stacks.Torsion

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Lemma 0A3Q.** In Situation 0A52 — `k` algebraically closed, `X` separated,
of finite type and of dimension at most one over `k` — assume `X` is reduced. Let `j : U → X` be
an open immersion, `ℓ` a prime, and `F = j_! 𝐙/ℓ𝐙` the extension by zero of the constant sheaf
on `U_étale` with value any abelian group `E` cyclic of order `ℓ`. Then statements (1) -- (8) of
Situation 0A52 hold for `F`, in the sense of `Stacks.EtaleCohomology.CurveStatements`, at every
coefficient universe and every `Ext` universe.

The sheaf `F` is killed by `ℓ`, hence torsion, so this is the reduction theorem
`curveStatements_of_torsionSheafProperty_max` applied with Lemma 0A5B on smooth curves
(`curveStatementsConstantOnSmoothCurves_of_prime`). -/
@[stacks 0A3Q]
theorem curveStatements_extensionByZero_constantSheaf_of_prime {k : Type u} [Field k]
    [IsAlgClosed k] {X U : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π]
    [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X] (hdim : topologicalKrullDim X ≤ 1)
    (j : U ⟶ X) [IsOpenImmersion j] {ℓ : ℕ} (hℓ : ℓ.Prime) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} π ((extensionByZero.{u, v} j).obj
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E)) := by
  have hE0 : ℓ • 𝟙 E = 0 := by
    obtain ⟨e⟩ := hE
    ext x
    apply e.injective
    simp [map_nsmul]
  have hF : ℓ • 𝟙 ((extensionByZero.{u, v} j).obj
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E)) = 0 :=
    nsmul_id_eq_zero_map (extensionByZero.{u, v} j)
      (nsmul_id_eq_zero_map (constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) hE0)
  exact curveStatements_of_torsionSheafProperty_max π hdim
    (fun p hp ↦ curveStatementsConstantOnSmoothCurves_of_prime k hp _ ⟨AddEquiv.ulift⟩) _
    (Stacks.Torsion.torsionSheafProperty_of_nsmul_id_eq_zero hℓ.pos hF)

end Stacks.EtaleCohomology

end
