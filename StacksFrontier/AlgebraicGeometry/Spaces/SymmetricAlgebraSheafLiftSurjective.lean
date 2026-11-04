module

public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraBundle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading

/-!
# The degree-one generators of `Sym(𝒢)` over an affine chart, and the lift `Sym(𝒢) ⟶ 𝒜`

Let `X` be an algebraic space and `𝒢` a quasi-coherent `𝒪_X`-module.  Over an affine étale chart
`V` the sections of `Sym(𝒢)` are the symmetric algebra `Sym_{𝒪_X(V)}(𝒢(V))`
(`AlgebraicGeometry.Space.symmetricAlgebraSheafSectionsRingEquiv`).  This file identifies the
degree-one generator `ι m` of the symmetric algebra of the sections with the image in the ungraded
realization of the degree-one generator of `Sym(𝒢)` applied to `m`, and deduces that the morphism
of algebra sheaves `Sym(𝒢) ⟶ 𝒜` induced by a morphism of modules `p : 𝒢 ⟶ 𝒜`
(`AlgebraicGeometry.Space.SymAlgSheaf.algebraLift`) is, over an affine chart, the lift of `p` out
of the symmetric algebra of the sections; in particular it is locally surjective when `p` is an
epimorphism of quasi-coherent modules.

## Main results

* `AlgebraicGeometry.Space.symmetricAlgebraSheafSectionsRingEquiv_ι`: the identification of the
  sections of `Sym(𝒢)` over an affine chart carries `ι m` to the degree-one generator at `m`.
* `AlgebraicGeometry.Space.algebraLift_symmetricAlgebraSheafSectionsRingEquiv_ι`: the lift takes
  the value `p m` there.
* `AlgebraicGeometry.Space.isLocallySurjective_of_surjective_affine`: a morphism of presheaves of
  rings on the small étale site surjective over the affine charts is locally surjective.
* `AlgebraicGeometry.Space.isLocallySurjective_algebraLift`: the lift is locally surjective when
  `p` is an epimorphism of quasi-coherent modules.

## References

* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of presheaves of rings on the small étale site of `X` which is surjective on the
sections over every affine étale chart is locally surjective. -/
theorem isLocallySurjective_of_surjective_affine {X : AlgebraicSpaces B S hS}
    {P Q : (SmallEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u}} (φ : P ⟶ Q)
    (hφ : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Function.Surjective (φ.app (op W))) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) φ := by
  refine ⟨fun {W} s => ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X.1 W)
  intro W' g hg
  obtain ⟨O, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  refine (Presheaf.imageSieve φ s).downward_closed ?_ a
  exact hφ _ (isAffine_chartScheme_openChart B S hS X.1 W O.down) _

variable {W : AlgebraicSpaces B S hS} (G : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- **The degree-one generator of `Sym(𝒢)` is the sheafification unit of the degree-one
generator of the sectionwise symmetric powers.** -/
theorem symmetricAlgebraGen_app_eq (V : (SmallEtale B S hS W.1)ᵒᵖ) (m : G.val.obj V) :
    (symmetricAlgebraGen B S hS W G).val.app V m =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
        (R := structureRingSheaf B S hS W) (𝟙 (structureRingSheaf B S hS W).obj)
        (PresheafOfModules.symPowInt (1 : ℤ) G.val)) V
          (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen G.val) V m) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (structureRingSheaf B S hS W).obj)
  have hinv : (symmetricAlgebraSheafificationIso B S hS W G).inv.val.app V m =
      PresheafOfModules.Hom.app (adj.unit.app G.val) V m := by
    have htri := congrArg (fun φ => PresheafOfModules.Hom.app φ V m)
      (adj.right_triangle_components G)
    have hinj : Function.Injective
        ((symmetricAlgebraSheafificationIso B S hS W G).hom.val.app V) := by
      intro a b hab
      have := congrArg ((symmetricAlgebraSheafificationIso B S hS W G).inv.val.app V) hab
      have h2 : ((symmetricAlgebraSheafificationIso B S hS W G).hom ≫
          (symmetricAlgebraSheafificationIso B S hS W G).inv).val.app V a =
        ((symmetricAlgebraSheafificationIso B S hS W G).hom ≫
          (symmetricAlgebraSheafificationIso B S hS W G).inv).val.app V b := this
      rwa [Iso.hom_inv_id] at h2
    exact hinj ((congrArg (fun φ => φ.val.app V m)
      (symmetricAlgebraSheafificationIso B S hS W G).inv_hom_id).trans htri.symm)
  have hu := (PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} G.val).sheafifyGen_unit
    (𝟙 (structureRingSheaf B S hS W).obj) (PresheafOfModules.symPowIntGen G.val) V m
  rwa [← hinv] at hu

variable (hG : G.IsQuasicoherentOnSite) (V : SmallEtale B S hS W.1)
  (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))

/-- **The identification of the sections of `Sym(𝒢)` over an affine chart with the symmetric
algebra of the sections of `𝒢` carries the degree-one generator `ι m` to the degree-one generator
of `Sym(𝒢)` at `m`.** -/
theorem symmetricAlgebraSheafSectionsRingEquiv_ι
    (m : (commStructureVal B S hS G).obj (op V)) :
    symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV
        (SymmetricAlgebra.ι _ _ m) =
      (symmetricAlgebra B S hS W G).ungradedIncl 1
        ((symmetricAlgebraGen B S hS W G).val.app (op V) m) := by
  have hmem := SymPow.ι_mem_symmetricPower
    (R := (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V)))
    (M := (commStructureVal B S hS G).obj (op V)) m
  have hdec : DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) (SymmetricAlgebra.ι _ _ m) =
      DirectSum.of (fun n : ℕ => (SymPow.symmetricPower n
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)) : Type u)) 1 ⟨_, hmem⟩ :=
    DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n
      (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
      ((commStructureVal B S hS G).obj (op V))) hmem
  have h1 : ofSymPowers B S hS W G hG V hV (DirectSum.of (fun n : ℕ => (SymPow.symmetricPower n
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
        ((commStructureVal B S hS G).obj (op V)) : Type u)) 1 ⟨_, hmem⟩) =
      (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.incl 1
        ((symmetricAlgebraGen B S hS W G).val.app (op V) m) := by
    refine (ofSymPowers_of B S hS W G hG V hV 1 ⟨_, hmem⟩).trans ?_
    refine (symPowerIncl_apply B S hS W G hG V hV 1 ⟨_, hmem⟩).trans ?_
    refine Eq.trans ?_ (congrArg ((symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.incl 1)
      (symmetricAlgebraGen_app_eq G (op V) m)).symm
    exact congrArg (DirectSum.of
      (fun k : ℤ => (((symmetricAlgebra B S hS W G).piece k).val.obj (op V) : Type u)) 1)
      (congrArg (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u}
        (R := structureRingSheaf B S hS W) (𝟙 (structureRingSheaf B S hS W).obj)
        (PresheafOfModules.symPowInt (1 : ℤ) G.val)) (op V))
        (Subtype.ext rfl))
  have h0 : symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV
      (SymmetricAlgebra.ι _ _ m) =
      (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.totalUnit
        (SmallEtale.topology B S hS W.1) (op V) (ofSymPowers B S hS W G hG V hV
          (DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n
            (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
            ((commStructureVal B S hS G).obj (op V))) (SymmetricAlgebra.ι _ _ m))) := rfl
  refine h0.trans ((congrArg (fun z =>
    (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.totalUnit
      (SmallEtale.topology B S hS W.1) (op V) (ofSymPowers B S hS W G hG V hV z)) hdec).trans ?_)
  exact congrArg (fun z => (symmetricAlgebra B S hS W G).toPresheafGradedAlgebra.totalUnit
    (SmallEtale.topology B S hS W.1) (op V) z) h1

variable {G} (𝒜 : AlgebraSheaf.{u, u} B S hS W.1 W.2) (p : G ⟶ AlgebraSheaf.underlyingModule 𝒜)

/-- **Over an affine chart the lift `Sym(𝒢) ⟶ 𝒜` takes the value `p m` on the degree-one
generator `ι m` of the symmetric algebra of the sections.** -/
theorem algebraLift_symmetricAlgebraSheafSectionsRingEquiv_ι
    (m : (commStructureVal B S hS G).obj (op V)) :
    ((SymAlgSheaf.algebraLift B S hS W 𝒜 G p).right.hom.app (op V)).hom
        (symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV (SymmetricAlgebra.ι _ _ m)) =
      p.val.app (op V) m :=
  (congrArg ((SymAlgSheaf.algebraLift B S hS W 𝒜 G p).right.hom.app (op V)).hom
    (symmetricAlgebraSheafSectionsRingEquiv_ι G hG V hV m)).trans
    (SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS W 𝒜 G p (op V) m)

/-- **Over an affine chart the lift `Sym(𝒢) ⟶ 𝒜` carries the structure map of the symmetric
algebra of the sections to the structure map of `𝒜`.** -/
theorem algebraLift_symmetricAlgebraSheafSectionsRingEquiv_algebraMap
    (r : (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) :
    ((SymAlgSheaf.algebraLift B S hS W 𝒜 G p).right.hom.app (op V)).hom
        (symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG V hV (algebraMap _ _ r)) =
      𝒜.algebraMap (op V) r :=
  (congrArg ((SymAlgSheaf.algebraLift B S hS W 𝒜 G p).right.hom.app (op V)).hom
    (symmetricAlgebraSheafSectionsRingEquiv_algebraMap B S hS W G hG V hV r)).trans
    ((SymAlgSheaf.algebraLift B S hS W 𝒜 G p).comm (op V) r)

include hG in
/-- **The lift `Sym(𝒢) ⟶ 𝒜` is locally surjective** when `p : 𝒢 ⟶ 𝒜` is an epimorphism of
quasi-coherent modules. -/
theorem isLocallySurjective_algebraLift (h𝒜 : 𝒜.IsQuasicoherent) (hp : Epi p) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1)
      (SymAlgSheaf.algebraLift B S hS W 𝒜 G p).right.hom := by
  refine isLocallySurjective_of_surjective_affine _ fun V hV a => ?_
  obtain ⟨m, hm⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite p hp hG h𝒜 V hV a
  exact ⟨_, (SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS W 𝒜 G p (op V) m).trans hm⟩

end AlgebraicGeometry.Space
