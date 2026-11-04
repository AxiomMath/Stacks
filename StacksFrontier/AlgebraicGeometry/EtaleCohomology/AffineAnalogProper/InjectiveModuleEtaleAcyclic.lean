module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionSectionsCorepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Injective sheaves of modules are acyclic on étale schemes over the base

Let `X` be a scheme, `𝒜` a sheaf of rings on `X_étale` and `ℐ` an injective sheaf of
`𝒜`-modules. For every étale morphism `j : W ⟶ X` the étale cohomology
`H^q(W, ℐ|_W)` of the restriction of the underlying abelian sheaf of `ℐ` vanishes in positive
degrees. This is the combination of Stacks 03F3, which identifies `H^q(W, ℐ|_W)` with the
cohomology of `ℐ` over the object `W ⟶ X` of `X_étale`, and Stacks 03FD, by which the underlying
abelian sheaf of an injective module has no higher cohomology over any object.

Concretely, `j^{-1}` has the exact left adjoint `j_!` and so preserves injective abelian sheaves,
whence `H^q(W, j^{-1} F) = Ext^q(j_! ℤ_W, F)`; the sheaf `j_! ℤ_W` corepresents the sections over
`W ⟶ X`, so it is the free abelian sheaf on that object, against which the underlying abelian
sheaf of an injective module has no higher `Ext`
(`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.ext_eq_zero_of_injective_toSheaf`).

The file also records that the underlying abelian sheaf of a sheaf of modules over a torsion sheaf
of rings is torsion, the condition under which Gabber's theorem (Stacks 09ZI) applies to it.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroZSheafIso` — `j_! ℤ_W` is the free abelian sheaf on the
  object `W ⟶ X` of `X_étale`.
* `Stacks.EtaleCohomology.subsingleton_H_etaleAbelianInverseImage_toSheaf_of_injective` —
  `H^q(W, ℐ|_W) = 0` for `q > 0`.
* `Stacks.EtaleCohomology.torsionSheafProperty_toSheaf_of_torsion` — torsion of the underlying
  abelian sheaf of a module over a torsion sheaf of rings.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0A51](https://stacks.math.columbia.edu/tag/0A51)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology


section InjectiveModules

variable {X W : Scheme.{u}} (j : W ⟶ X) [Etale j]

/-- The object `W ⟶ X` of the small étale site of `X`, as the image of the final object of the
small étale site of `W` under composition with `j`. -/
abbrev etaleObjectOf : X.Etale := (Scheme.Etale.smallEtaleCompose j).obj (finalObj W)

/-- **`j_! ℤ_W` is the free abelian sheaf on the object `W ⟶ X`.** Both corepresent the
sections over `W ⟶ X`: the first through the adjunction `j_! ⊣ j^{-1}` and the corepresentation
of global sections by the constant sheaf `ℤ_W`, the second directly. -/
def extensionByZeroZSheafIso :
    (extensionByZero.{u, 0} j).obj (zSheaf W) ≅
      (Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{u + 1} X.smallEtaleTopology).obj
        (etaleObjectOf j) := by
  let e₁ := Stacks.Cohomology.ExtComparison.compPreadditiveCoyonedaIso
    (extensionByZeroAdj.{u, 0} j) (zSheaf W)
  let e₂ := Functor.isoWhiskerLeft (etaleRestriction.{u, 0} j)
    (sectionsCorepresentation (finalObj_isTerminal W))
  let e₃ : etaleRestriction.{u, 0} j ⋙ sectionsOver (finalObj W) ≅
      sectionsOver (etaleObjectOf j) := NatIso.ofComponents (fun _ => Iso.refl _)
  let e₄ := Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation.{u + 1}
    X.smallEtaleTopology (etaleObjectOf j)
  exact (preadditiveCoyoneda.preimageIso (e₁.symm ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄)).unop.symm

/-- Restriction along an étale morphism `j` preserves injective abelian sheaves. -/
instance : (etaleRestriction.{u, 0} j).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extensionByZeroAdj.{u, 0} j)

/-- Restriction along an étale morphism `j` preserves finite colimits. -/
instance : PreservesFiniteColimits (etaleRestriction.{u, 0} j) :=
  have : (etaleRestriction.{u, 0} j).IsLeftAdjoint := (etaleDirectImageAdj.{u, 0} j).isLeftAdjoint
  inferInstance

/-- **Stacks 03F3 and 03FD on the small étale site.** For an étale `j : W ⟶ X`, a sheaf of rings
`𝒜` on `X_étale` and an injective sheaf of `𝒜`-modules `ℐ`, the restriction to `W` of the
underlying abelian sheaf of `ℐ` has no étale cohomology in positive degrees. -/
theorem subsingleton_H_etaleRestriction_toSheaf_of_injective
    (𝒜 : Sheaf X.smallEtaleTopology RingCat.{u + 1}) (ℐ : SheafOfModules.{u + 1} 𝒜)
    [Injective ℐ] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((etaleRestriction.{u, 0} j).obj ((SheafOfModules.toSheaf 𝒜).obj ℐ)) q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale.{u, u} X
  have : IsGrothendieckAbelian.{u + 1} (Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale.{u, u} W
  let e := (Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (extensionByZeroAdj.{u, 0} j) (extensionByZeroZSheafIso j) (n + 1)).app
      ((SheafOfModules.toSheaf 𝒜).obj ℐ)
  exact e.symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
    (subsingleton_of_forall_eq 0
      (Stacks.Cohomology.InjectiveModuleSheafAcyclicity.ext_eq_zero_of_injective_toSheaf.{u + 1}
        X.smallEtaleTopology 𝒜 ℐ (etaleObjectOf j) n))

/-- **Stacks 03F3 and 03FD on the small étale site**, for the inverse image: `H^q(W, j^{-1} ℐ) = 0`
for `q > 0`, `j : W ⟶ X` étale and `ℐ` an injective sheaf of modules on `X_étale`. -/
theorem subsingleton_H_etaleAbelianInverseImage_toSheaf_of_injective
    (𝒜 : Sheaf X.smallEtaleTopology RingCat.{u + 1}) (ℐ : SheafOfModules.{u + 1} 𝒜)
    [Injective ℐ] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} j).obj ((SheafOfModules.toSheaf 𝒜).obj ℐ)) q) :=
  Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    ((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app _).symm q
    (subsingleton_H_etaleRestriction_toSheaf_of_injective j 𝒜 ℐ q hq)

end InjectiveModules

end Stacks.EtaleCohomology

namespace Stacks.Torsion

universe w v u'

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A module over a torsion sheaf of rings is torsion.** If every local section of the sheaf of
rings `R` is locally killed by a positive integer, then so is every local section of an
`R`-module `M`: the unit `1` is killed by `n` on a covering, hence so is every section of `M`
there. -/
theorem torsionSheafProperty_toSheaf_of_torsion (R : Sheaf J RingCat.{w})
    (hR : torsionSheafProperty J ((sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj R))
    (M : SheafOfModules.{w} R) :
    torsionSheafProperty J ((SheafOfModules.toSheaf R).obj M) := by
  intro U x
  obtain ⟨S, hS, hS'⟩ := hR U (1 : R.obj.obj (op U))
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨n, hn, h⟩ := hS' V f hf
  refine ⟨n, hn, ?_⟩
  have h1 : (n • (1 : R.obj.obj (op V))) = 0 := by
    have : (R.obj.map f.op) (1 : R.obj.obj (op U)) = 1 := map_one _
    rw [← this]
    exact h
  have key : ∀ m : M.val.obj (op V), n • m = (n • (1 : R.obj.obj (op V))) • m := fun m => by
    rw [smul_assoc, one_smul]
  have h2 := key (M.val.map f.op x)
  rw [h1] at h2
  exact h2.trans (zero_smul (R.obj.obj (op V)) _)

end Stacks.Torsion
