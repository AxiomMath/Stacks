module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.Separable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GaloisFixedComponentDescent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentityComponent

/-!
# Irreducible components through the identity of a group scheme

Every irreducible component of a group scheme over a field which contains the identity is
geometrically irreducible over the field.  After extension to a separable closure the identity
point is Galois-fixed, so the unique irreducible component through it is fixed as well, and
descent of fixed geometric components identifies it with the base change of a geometrically
irreducible component; that component contains the identity, hence is the one given.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_irreducibleComponent_of_identity`: an irreducible
  component containing the identity is geometrically irreducible.

## Implementation notes

An irreducible component is represented by an element of `irreducibleComponents G`.  To regard
its underlying closed subset as a scheme, it is equipped with the reduced induced subscheme
structure defined by its vanishing ideal.  The condition that the component passes through the
identity is expressed by containment of the range of the unit section.

## References

* [Stacks Project, Tag 047M](https://stacks.math.columbia.edu/tag/047M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- The identity point of a base-changed group scheme is fixed by the Galois action on the
base change. -/
private theorem identityPoint_fixed_galoisAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : Grp (Over (Spec (.of k)))) (σ : K ≃ₐ[k] K) :
    Scheme.forget.map
      ((galoisActionOnBaseChange k K G.X).ρ (MulOpposite.op σ)).asHom
      (identityPoint K ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj G)) =
    identityPoint K ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj G) := by
  let _ : GrpObj (Over.mk G.X.hom) := G.grp
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : GrpObj (Over.mk (pullback.snd G.X.hom g)) := Over.grpObjMkPullbackSnd
  let unit := η[Over.mk (pullback.snd G.X.hom g)].left
  have hfst : unit ≫ pullback.fst G.X.hom g = g ≫ η[G.X].left := by
    dsimp [unit]
    rw [CategoryTheory.Over.grpObjMkPullbackSnd_one, CategoryTheory.Over.comp_left,
      CategoryTheory.Over.ε_pullback_left]
    change (inv (pullback.snd (𝟙 (Spec (.of k))) g) ≫
        ((Over.pullback g).map (η[G.X])).left) ≫ pullback.fst G.X.hom g = _
    dsimp [CategoryTheory.Over.pullback]
    have hproj : inv (pullback.snd (𝟙 (Spec (.of k))) g) ≫
        pullback.fst (𝟙 (Spec (.of k))) g = g := by
      rw [show pullback.fst (𝟙 (Spec (.of k))) g = pullback.snd (𝟙 (Spec (.of k))) g ≫ g by
        simpa using pullback.condition (f := 𝟙 (Spec (.of k))) (g := g)]
      simp
    change (inv (pullback.snd (𝟙 (Spec (.of k))) g) ≫
      pullback.lift (pullback.fst (𝟙 (Spec (.of k))) g ≫ η[G.X].left)
        (pullback.snd (𝟙 (Spec (.of k))) g) _ ≫ pullback.fst G.X.hom g) = _
    rw [pullback.lift_fst, ← Category.assoc, hproj]
  have hsnd : unit ≫ pullback.snd G.X.hom g = 𝟙 (Spec (.of K)) :=
    Over.Hom.w (η[Over.mk (pullback.snd G.X.hom g)])
  let s := Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)
  let a := (galoisActionOnBaseChange k K G.X).ρ (MulOpposite.op σ) |>.asHom
  have hfstA : a ≫ pullback.fst G.X.hom g = pullback.fst G.X.hom g := by
    dsimp [a, galoisActionOnBaseChange]
    rw [pullback.map, pullback.lift_fst]
    rfl
  have hsndA : a ≫ pullback.snd G.X.hom g = pullback.snd G.X.hom g ≫ s := by
    dsimp [a, s, galoisActionOnBaseChange]
    rw [pullback.map, pullback.lift_snd]
    rfl
  have hs : s ≫ g = g := specMapAlgAut_comp_structureMap k K σ
  have hcomp : unit ≫ a = s ≫ unit := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hfstA, hfst, ← Category.assoc, hs]
    · rw [Category.assoc, Category.assoc, hsndA, ← Category.assoc, hsnd]
      simp
  let e := (Over.tensorUnit_left (C := Scheme) (X := Spec (.of K))).symm ▸
    (default : Spec (.of K))
  have hpt := congrArg (fun q => (Scheme.forget.map q) e) hcomp
  change (Scheme.forget.map a) ((Scheme.forget.map unit) e) =
    (Scheme.forget.map unit) e
  have hpt' : (Scheme.forget.map a) ((Scheme.forget.map unit) e) =
      (Scheme.forget.map unit) ((Scheme.forget.map s) e) := by
    simpa only [Functor.map_comp, CategoryTheory.comp_apply] using hpt
  have : Subsingleton (Scheme.forget.obj (Spec (.of K))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  rwa [Subsingleton.elim ((Scheme.forget.map s) e) e] at hpt'

/-- A bundled group scheme over a field has a unique irreducible component containing its
identity point. -/
@[sga "3 VIA 2.6.1" "Clause (i), special case"]
private theorem existsUnique_identityComponent
    (R : Type u) [Field R] (G : Grp (Over (Spec (.of R)))) :
    ∃! Z : irreducibleComponents G.X.left,
      identityPoint R G ∈ (Z : Set G.X.left) := by
  let _ : GrpObj (Over.mk G.X.hom) := G.grp
  have h : (default : Spec (.of R)) = IsLocalRing.closedPoint R := Subsingleton.elim _ _
  simpa [identityPoint, h] using
    (existsUnique_irreducibleComponent_containing_identity
      (G.X.hom : G.X.left ⟶ Spec (.of R)))

/-- **Stacks Project, Tag 047M.** An irreducible component of a group scheme over a field
which contains the identity is geometrically irreducible over that field. -/
@[stacks 047M "identity_component_geometrically_irreducible",
  sga "3 VIA 2.4" "(i) geom. irred., field",
  sga "3 VIA 2.6.5" "(ii) geom. irreducible",
  sga "3 VIA 2.6.2"]
theorem geometricallyIrreducible_irreducibleComponent_of_identity
    (k : Type u) [Field k] (G : Scheme.{u}) (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] (Z : irreducibleComponents G)
    (he : Set.range (η[Over.mk f]).left ⊆ Z.1) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ :
          TopologicalSpace.Closeds G)).subschemeι ≫ f) := by
  let G₀ : Grp (Over (Spec (.of k))) := Grp.mk (Over.mk f)
  let eₖ := (Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸
    (default : Spec (.of k))
  have hIdZ : identityPoint k G₀ ∈ (Z : Set G) := he ⟨eₖ, rfl⟩
  let K := SeparableClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : GrpObj (Over.mk (pullback.snd f g)) := Over.grpObjMkPullbackSnd
  let Gₖ : Grp (Over (Spec (.of K))) := (Over.pullback g).mapGrp.obj G₀
  obtain ⟨Cₖ, hCₖ, hCₖunique⟩ := existsUnique_identityComponent K Gₖ
  let Act := galoisActionOnGeometricIrreducibleComponents k K G₀.X
  let Cbar : Act.V := ⟨Cₖ.1, Cₖ.2⟩
  have hfixed : ∀ σ : MulOpposite (K ≃ₐ[k] K),
      ConcreteCategory.hom (Act.ρ σ).asHom Cbar = Cbar := by
    intro σ
    let Y : irreducibleComponents Gₖ.X.left := ConcreteCategory.hom (Act.ρ σ).asHom Cbar
    have hY : identityPoint K Gₖ ∈ (Y : Set Gₖ.X.left) := by
      change identityPoint K Gₖ ∈ (ConcreteCategory.hom (Act.ρ σ).asHom Cbar).1
      rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe]
      exact ⟨identityPoint K Gₖ, hCₖ, by
        simpa [G₀, Gₖ, Act] using identityPoint_fixed_galoisAction k K G₀ σ.unop⟩
    exact hCₖunique Y hY
  obtain ⟨T, hTgeom, hTpre⟩ :=
    fixed_geometricComponent_iff_exists_geometricallyIrreducible_component
      k K G f Cbar |>.mp hfixed
  obtain ⟨D, -, hDunique⟩ := existsUnique_identityComponent k G₀
  have hTid : identityPoint k G₀ ∈ (T : Set G) := by
    have hpre : identityPoint K Gₖ ∈ (pullback.fst f g).base ⁻¹' (T : Set G) := by
      rwa [hTpre]
    have hmap : (pullback.fst f g).base (identityPoint K Gₖ) = identityPoint k G₀ := by
      simpa [G₀, Gₖ, g] using identityPoint_baseChange_fst k K G₀
    change (pullback.fst f g).base (identityPoint K Gₖ) ∈ (T : Set G) at hpre
    rwa [hmap] at hpre
  cases (hDunique T hTid).trans (hDunique Z hIdZ).symm
  exact hTgeom

end AlgebraicGeometry

end
