module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage

/-!
# The eight statements do not depend on the universe of `Ext`

Statements (1) -- (8) of Situation 0A52, `Stacks.EtaleCohomology.CurveStatements`, are phrased
with étale cohomology `Sheaf.H.{w}`, the `Ext`-groups out of the constant sheaf computed in a
chosen universe `w`. Changing `w` changes these groups only up to the canonical bijection
`Abelian.Ext.chgUniv`, which commutes with the restriction maps; hence the eight statements hold
in one universe exactly when they hold in another.

## Main results

* `Stacks.EtaleCohomology.ext_chgUniv_mapExactFunctor`: an exact functor induces the same map on
  `Ext` whatever the universe in which the source `Ext` is computed.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_chgUniv`: restriction commutes with the
  change of universe.
* `Stacks.EtaleCohomology.CurveStatements.chgUniv`: the eight statements in one `Ext` universe
  give them in any other.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe w w₁ w' u v

namespace Stacks.EtaleCohomology

/-- **An exact functor induces the same map on `Ext` in every source universe.** -/
theorem ext_chgUniv_mapExactFunctor {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w₁} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (e : Ext.{w} X Y n) :
    ((Ext.chgUniv.{w₁} e).mapExactFunctor F : Ext.{w'} (F.obj X) (F.obj Y) n) =
      e.mapExactFunctor F := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  ext
  simp only [Ext.mapExactFunctor_hom, Ext.homEquiv_chgUniv]

/-- **Restriction on étale cohomology commutes with the change of `Ext` universe.** -/
theorem etaleCohomologyRestrictionMap_chgUniv {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    etaleCohomologyRestrictionMap.{u, v, w₁} i F q (Ext.chgUniv.{w₁} x) =
      Ext.chgUniv.{w₁} (etaleCohomologyRestrictionMap.{u, v, w} i F q x) := by
  rw [etaleCohomologyRestrictionMap_apply, etaleCohomologyRestrictionMap_apply]
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  let := HasDerivedCategory.standard (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom, Ext.homEquiv_chgUniv]


/-- Restriction composed with the change of `Ext` universe, as a composite of functions. -/
private theorem etaleCohomologyRestrictionMap_comp_chgUniv {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    ⇑(etaleCohomologyRestrictionMap.{u, v, w₁} i F q) ∘
      (Ext.chgUniv.{w₁} : Sheaf.H.{w} F q ≃ Sheaf.H.{w₁} F q) =
        Ext.chgUniv.{w₁} ∘ etaleCohomologyRestrictionMap.{u, v, w} i F q :=
  funext fun x ↦ etaleCohomologyRestrictionMap_chgUniv.{w, w₁, u, v} i F q x

/-- Bijectivity of restriction does not depend on the `Ext` universe. -/
theorem bijective_etaleCohomologyRestrictionMap_chgUniv {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (hq : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i F q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w₁} i F q) :=
  (Function.Bijective.of_comp_iff _
    (Ext.chgUniv.{w₁} : Sheaf.H.{w} F q ≃ Sheaf.H.{w₁} F q).bijective).1
    (by rw [etaleCohomologyRestrictionMap_comp_chgUniv.{w, w₁, u, v} i F q]
        exact Ext.chgUniv.bijective.comp hq)

/-- Surjectivity of restriction does not depend on the `Ext` universe. -/
theorem surjective_etaleCohomologyRestrictionMap_chgUniv {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w₁} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (hq : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i F q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w₁} i F q) :=
  Function.Surjective.of_comp (g := (Ext.chgUniv.{w₁} : Sheaf.H.{w} F q ≃ Sheaf.H.{w₁} F q))
    (by rw [etaleCohomologyRestrictionMap_comp_chgUniv.{w, w₁, u, v} i F q]
        exact Ext.chgUniv.surjective.comp hq)

/-- **The eight statements do not depend on the `Ext` universe.** If `Ext` of abelian sheaves on
the small étale site of every scheme exists in the universe `w`, statements (1) -- (8) of
Situation 0A52 computed with `Ext` in `w` give them computed in any universe `w₁`. -/
theorem CurveStatements.chgUniv {k : Type u} [Field k] {X : Scheme.{u}} {π : X ⟶ Spec (.of k)}
    (hExt : ∀ S : Scheme.{u}, HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (h : letI := hExt X; CurveStatements.{u, v, w} π F) : CurveStatements.{u, v, w₁} π F := by
  let := hExt X
  have hsub : ∀ q, Subsingleton (Sheaf.H.{w} F q) → Subsingleton (Sheaf.H.{w₁} F q) :=
    fun q hq ↦ (Ext.chgUniv.{w} : Sheaf.H.{w₁} F q ≃ Sheaf.H.{w} F q).subsingleton
  have hfin : ∀ q, Finite (Sheaf.H.{w} F q) → Finite (Sheaf.H.{w₁} F q) :=
    fun q hq ↦ Finite.of_equiv _ (Ext.chgUniv.{w₁} : Sheaf.H.{w} F q ≃ Sheaf.H.{w₁} F q)
  exact
    { vanishing := fun q hq ↦ hsub q (h.vanishing q hq)
      affineVanishing := fun hX q hq ↦ hsub q (h.affineVanishing hX q hq)
      primePowerVanishing := fun p _ hp ht q hq ↦ hsub q (h.primePowerVanishing p hp ht q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun B hX _ _ hc ht q ↦
        hfin q (h.finite_of_isPrimeToCharacteristicTorsion B hX hc ht q)
      finite_of_isProper := fun B hX _ _ hπ hc q ↦ hfin q (h.finite_of_isProper B hX hπ hc q)
      bijective_of_isPrimeToCharacteristicTorsion := fun ht k' _ _ _ _ _ q ↦
        bijective_etaleCohomologyRestrictionMap_chgUniv _ _ q
          (let := hExt (scalarExtension k k' π);
            h.bijective_of_isPrimeToCharacteristicTorsion ht k' q)
      bijective_of_isProper := fun hπ k' _ _ _ _ _ q ↦
        bijective_etaleCohomologyRestrictionMap_chgUniv _ _ q
          (let := hExt (scalarExtension k k' π); h.bijective_of_isProper hπ k' q)
      surjective := fun U _ ↦
        surjective_etaleCohomologyRestrictionMap_chgUniv _ _ 2 (let := hExt U; h.surjective U) }

/-- **Statements (1) -- (8) at the coefficients `AddCommGrpCat.{u + 1}` in any `Ext` universe**
from those with `Ext` in `u + 1`. -/
theorem CurveStatements.ofSucc {k : Type u} [Field k] {X : Scheme.{u}} {π : X ⟶ Spec (.of k)}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    [HasExt.{w₁} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (h : letI := hasExt_sheaf_smallEtale_succ X; CurveStatements.{u, 0, u + 1} π F) :
    CurveStatements.{u, 0, w₁} π F :=
  CurveStatements.chgUniv.{u + 1, w₁, u, 0} hasExt_sheaf_smallEtale_succ h

end Stacks.EtaleCohomology
