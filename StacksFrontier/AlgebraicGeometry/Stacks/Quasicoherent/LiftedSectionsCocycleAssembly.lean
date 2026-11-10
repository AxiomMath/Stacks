module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilySheafCondition
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentBaseChangeComp

/-!
# The cocycle condition for the sections identification of Stacks 076T

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean` carries
one hypothesis, `AlgebraicGeometry.Stack.LiftedSectionsCocycle`: that the five-factor
identification of sections `AlgebraicGeometry.Stack.liftedSectionsIso` is compatible with
composition of arrows of `𝒳`.  This file reduces that hypothesis to the composition law for
*factor 4 alone*.

## The split

`AlgebraicGeometry.Stack.liftedSectionsIso` is a composite of five identifications.  The last
two of them — the base-change identification of **Stacks 03DS** read backwards, and the
restriction map along the arrow of `Sch/U` identifying `W / U` with the final object of the
small étale site of `W` seen over `U` — form an isomorphism, and
`AlgebraicGeometry.Stack.liftedSectionsIso_hom_eq` splits the identification as
`AlgebraicGeometry.Stack.liftedSectionsUpper` followed by it.  Their composition law is
`Stacks.Sites.baseChangeCompIso_inv_restriction`, available unconditionally; what remains is the
square for `AlgebraicGeometry.Stack.liftedSectionsUpper`, whose right-hand vertical is forced to
be the left-hand vertical of that law.

That square is carried here as
`AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn`, a *stand-in* for the
composition law of factors 2, 3 and 4 read on sections over the final object of the small étale
site.  No Stacks tag is registered on anything carrying it.

What is missing is not the composition law.  That law is stated, unconditionally and twice, at
the level of sheaves of modules on the small étale site:
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_comp` is the law for factor
4 alone, and `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp` is the law for factors 2, 3
and 4 together, for the morphism of sheaves of modules
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` which those three factors are the inverse of
by `AlgebraicGeometry.Stack.liftedSmallEtaleIso_hom_comp_sheafInv`.

What is missing is the passage from a law about morphisms of sheaves to the square below, which
is about their *sections at one object*.  Two of the three steps of that passage are available:
`AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_sheafifiedFactor` reads factors 3 and 4
on sections over the final object, which the Stacks 06WC pullback of presheaves of modules being
a left adjoint would otherwise forbid, and
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module` is the
naturality in the module that the vertical at the associated-module stage needs.  The step still
missing is a compatibility on sections between the base-change identification
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` of **Stacks 03LC (1)** and
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` of **Stacks 03DS**.  That one step, and
nothing else, is what the square below still wants:
`AlgebraicGeometry.Stack.liftedSectionsFactorFourSquare_of_compat` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedSectionsFactorFourReduction.lean`
derives the square from it alone, where it is carried as
`AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat`.

## What is *not* assumed

Nothing is added beyond that one square.  In particular the comparison map `c_φ` of
**Stacks 06WC** is assumed invertible only at the two arrows `φ` and `φ'` the cocycle condition
mentions, as `AlgebraicGeometry.Stack.LiftedSectionsCocycle` does: clause (b) of
**Stacks 06WK** — invertibility over the whole slice `𝒳/x` — is strictly stronger than
hypothesis (b) of Stacks 076T and is nowhere used.

## Main definitions

* `Stacks.Sites.pullbackCompSectionsIsoOfEq`: the composition isomorphism of the pullback
  pseudofunctor on global sections, at a morphism only *equal* to the composite.
* `AlgebraicGeometry.Stack.liftedSectionsUpper`: the first four factors of
  `AlgebraicGeometry.Stack.liftedSectionsIso`.
* `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn`: **the one square carried** —
  the stand-in for the composition law of factor 4.

## Main results

* `Stacks.Sites.baseChangeCompIso_inv_restriction_of_eq`: the composition square of the
  base-change identification, at a morphism only equal to the composite, which is the shape the
  arrows below a composable pair of arrows of `𝒳` arrive in.
* `AlgebraicGeometry.Stack.liftedSectionsIso_hom_eq`: the split of the identification.
* `AlgebraicGeometry.Stack.liftedSectionsCocycle_of_factorFourSquare`: **the carried hypothesis
  of `LiftedFppfFamilySheafCondition.lean` follows from the factor-4 square alone.**

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Sites

variable {U W W' : Scheme.{u}} (𝓕 : U.Modules) (g : W ⟶ U) (k : W' ⟶ W) (g' : W' ⟶ U)

/-- The composition isomorphism of the pullback pseudofunctor on global sections, read at a
morphism `g'` which is only *equal* to the composite `k ≫ g` rather than being it. -/
noncomputable def pullbackCompSectionsIsoOfEq (hg' : g' = k ≫ g) (A : Over W') :
    Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback k).obj
        ((Scheme.Modules.pullback g).obj 𝓕)), ⊤) ≅
      Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback g').obj 𝓕), ⊤) :=
  sectionsTopIso ((Scheme.Modules.pullback A.hom).mapIso
    ((Scheme.Modules.pullbackComp k g).app 𝓕 ≪≫
      ((Scheme.Modules.pullbackCongr hg').app 𝓕).symm))

/-- At the composite `k ≫ g` itself, with `rfl` as the equality, `pullbackCompSectionsIsoOfEq` is
`pullbackCompSectionsIso`. -/
lemma pullbackCompSectionsIsoOfEq_rfl (A : Over W') :
    pullbackCompSectionsIsoOfEq 𝓕 g k (k ≫ g) rfl A = pullbackCompSectionsIso 𝓕 g k A := by
  refine Iso.ext ?_
  change ((Scheme.Modules.pullback A.hom).map
      ((Scheme.Modules.pullbackComp k g).hom.app 𝓕 ≫
        ((Scheme.Modules.pullbackCongr (rfl : k ≫ g = k ≫ g)).app 𝓕).inv)).app ⊤ = _
  rw [show ((Scheme.Modules.pullbackCongr (rfl : k ≫ g = k ≫ g)).app 𝓕).inv = 𝟙 _ from rfl,
    Category.comp_id]
  rfl

variable [𝓕.IsQuasicoherent]

/-- `Stacks.Sites.baseChangeCompIso_inv_restriction` at a morphism `g'` which is only *equal* to
the composite `k ≫ g`. -/
theorem baseChangeCompIso_inv_restriction_of_eq (hg' : g' = k ≫ g)
    {A : Over W} {A' : Over W'}
    (n : (Over.map k).obj A' ⟶ A)
    (e : (Over.mk g : Over U) ⟶ (Over.map g).obj A)
    (e' : (Over.mk g' : Over U) ⟶ (Over.map g').obj A')
    (m : (Over.mk g' : Over U) ⟶ Over.mk g)
    (hm : m.left ≫ e.left = e'.left ≫ n.left) :
    (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op A) ≫
        ((quasiCoherentPresheafFunctor W ((Scheme.Modules.pullback g).obj 𝓕)).map n.op ≫
          (quasiCoherentPresheafBaseChangeIso ((Scheme.Modules.pullback g).obj 𝓕)
            (Over.mk k)).hom.app (op A') ≫
          (pullbackCompSectionsIsoOfEq 𝓕 g k g' hg' A').hom) ≫
        ((quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g')).inv.app (op A') ≫
          (quasiCoherentPresheafFunctor U 𝓕).map e'.op) =
      (quasiCoherentPresheafFunctor U 𝓕).map (m ≫ e).op := by
  subst hg'
  rw [pullbackCompSectionsIsoOfEq_rfl]
  have key := baseChangeCompIso_inv_restriction 𝓕 g k n e e' m hm
  rw [show (baseChangeCompIso 𝓕 g k A').inv =
      (pullbackCompSectionsIso 𝓕 g k A').hom ≫
        (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk (k ≫ g))).inv.app (op A') from rfl,
    Category.assoc] at key
  exact key

end Stacks.Sites

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

/-- The composite of the first four factors of `AlgebraicGeometry.Stack.liftedSectionsIso`:
the sections of `F` at `z` read as the sections of the presheaf of **Stacks 03DS** of `g^*𝓕`
over the final object of the small étale site of `W`. -/
noncomputable def liftedSectionsUpper {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    F.presheaf.obj (op z) ⟶
      (quasiCoherentPresheafFunctor (p.obj z).left.1
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).obj
        (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
          (smallEtaleFinal B E h S hS p z))) :=
  (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).inv ≫
    (liftedSmallEtaleIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom.app
      (op (smallEtaleFinal B E h S hS p z)) ≫
    (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1 (contains_base B E h S hS p z)
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom.app
      (op (smallEtaleFinal B E h S hS p z))

/-- `AlgebraicGeometry.Stack.liftedSectionsIso` is
`AlgebraicGeometry.Stack.liftedSectionsUpper` followed by the base-change identification of
**Stacks 03DS**, read backwards, and the restriction map along the arrow of `Sch/U` which
identifies `W / U` with the final object of the small étale site of `W` seen over `U`. -/
theorem liftedSectionsIso_hom_eq {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    letI := h𝓕
    ∃ e : (Over.mk (B.inclusion.map (p.map φ).left) : Over (p.obj x).left.1) ⟶
        (Over.map (B.inclusion.map (p.map φ).left)).obj
          ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
            (smallEtaleFinal B E h S hS p z)),
      e.left = 𝟙 _ ∧
      (liftedSectionsIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom =
        liftedSectionsUpper B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso ≫
          ((Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓕
              (Over.mk (B.inclusion.map (p.map φ).left))).inv.app
            (op ((SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
              (smallEtaleFinal B E h S hS p z))) ≫
            (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map e.op) := by
  let := h𝓕
  refine ⟨(Over.isoMk (Iso.refl _)
    (by simp)).hom, rfl, ?_⟩
  unfold liftedSectionsIso liftedSectionsUpper
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rfl

/-- **Stand-in, not a result: the composition law for factor 4 of
`AlgebraicGeometry.Stack.liftedSectionsIso`**, in the only form the assembly of the cocycle
condition consumes.

Factors 1, 2, 3, 4 and 5a of the identification compose into
`AlgebraicGeometry.Stack.liftedSectionsUpper`; of their composition laws every one but factor
4's is available. This is the square those laws paste into: at a composable pair of arrows both
lying over a morphism along which the comparison map of **Stacks 06WC** is an isomorphism,
restriction of `F` along `ψ` followed by the identification at `ψ ≫ φ` is the identification at
`φ` followed by the right-hand vertical of factor 5's square — restriction along the arrow `n`
of `Sch/W`, base change along the morphism `k` below `ψ`, and the composition isomorphism of the
pullback pseudofunctor.

No Stacks tag may be registered on anything which carries this. -/
def LiftedSectionsFactorFourSquareStandIn : Prop :=
  ∀ (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) {x : 𝒳}
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x)
    (hkg : B.inclusion.map (p.map (ψ ≫ φ)).left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F))
    (hiso' : IsIso (restrictModulePullbackComparison B E h S hS p hp (ψ ≫ φ) (etaleTopology B)
      (etaleTopology_le_topology B) F))
    (n : (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z)),
    letI := h𝓕
    F.presheaf.map ψ.op ≫ liftedSectionsUpper B E h S hS p hp F hlqc (ψ ≫ φ) 𝓕 hMx eU hiso' =
      liftedSectionsUpper B E h S hS p hp F hlqc φ 𝓕 hMx eU hiso ≫
        (quasiCoherentPresheafFunctor (p.obj z).left.1
              ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).map n.op ≫
          (Stacks.Sites.quasiCoherentPresheafBaseChangeIso
              ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)
              (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
            (op ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
              (smallEtaleFinal B E h S hS p z'))) ≫
          (Stacks.Sites.pullbackCompSectionsIsoOfEq 𝓕 (B.inclusion.map (p.map φ).left)
              (B.inclusion.map (p.map ψ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left) hkg
              ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
                (smallEtaleFinal B E h S hS p z'))).hom

/-- The arrow of the schemes over `W` from the base change along the morphism below `ψ` of the
final object of the small étale site of `W'` to the final object of the small étale site of
`W`: both structure morphisms are identities, so it is the morphism below `ψ` itself. -/
noncomputable def finalBaseChangeArrow {z' z : 𝒳} (ψ : z' ⟶ z) :
    (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z) :=
  Over.homMk (B.inclusion.map (p.map ψ).left)
    (by simp [smallEtaleFinal, SmallEtale.final, Over.post])

/-- The underlying morphism of `finalBaseChangeArrow` is the morphism below `ψ`. -/
@[simp]
theorem finalBaseChangeArrow_left {z' z : 𝒳} (ψ : z' ⟶ z) :
    (finalBaseChangeArrow B E h S hS p ψ).left = B.inclusion.map (p.map ψ).left :=
  rfl

/-- The arrow of the schemes over `U` below `ψ`, from the morphism below `φ'` to the morphism
below `φ`. -/
noncomputable def belowArrow {x z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x)
    (hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left) :
    (Over.mk (B.inclusion.map (p.map φ').left) : Over (p.obj x).left.1) ⟶
      Over.mk (B.inclusion.map (p.map φ).left) :=
  Over.homMk (B.inclusion.map (p.map ψ).left) hkg.symm

/-- The arrow of the big fppf site of the scheme below `x` which the cocycle condition compares
along: the image of `ψ`, from the image of `φ'` to the image of `φ`. -/
noncomputable def belowArrowSite {x z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x)
    (hφ' : φ' = ψ ≫ φ) :
    (Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ') :
        Over ((p ⋙ Over.forget (B.obj hS)).obj x)) ⟶
      Over.mk ((p ⋙ Over.forget (B.obj hS)).map φ) :=
  Over.homMk ((p ⋙ Over.forget (B.obj hS)).map ψ) (by simp [hφ'])

/-- The underlying morphism of `belowArrow` is the morphism below `ψ`. -/
@[simp]
theorem belowArrow_left {x z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x)
    (hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left) :
    (belowArrow B S hS p ψ φ φ' hkg).left = B.inclusion.map (p.map ψ).left :=
  rfl

/-- The pasting of the two squares, with every object and arrow abstract: the identification
split as `u` followed by an invertible `dinv` and a tail `ee`, a square `hA` for `u` and a
square `hB` for the rest. -/
private theorem paste_squares {C : Type*} [Category C] {P P' Q Q' R T T' : C}
    (fψ : P ⟶ P') (u : P ⟶ Q) (u' : P' ⟶ Q') (v : Q ⟶ Q')
    (dinv : Q ⟶ R) (dhom : R ⟶ Q) (ee : R ⟶ T) (tail' : Q' ⟶ T') (mapme : R ⟶ T')
    (mm : T ⟶ T')
    (hA : fψ ≫ u' = u ≫ v)
    (hB : dhom ≫ v ≫ tail' = mapme)
    (hC : mapme = ee ≫ mm)
    (hD : dinv ≫ dhom = 𝟙 Q) :
    fψ ≫ u' ≫ tail' = (u ≫ dinv ≫ ee) ≫ mm := by
  rw [← Category.assoc, hA, Category.assoc, Category.assoc, Category.assoc, ← hC, ← hB,
    ← Category.assoc dinv dhom, hD, Category.id_comp]

/-- **The cocycle condition for `AlgebraicGeometry.Stack.liftedSectionsIso`, over the factor-4
stand-in.** Pasting the stand-in square of
`AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn` onto the composition square of
`Stacks.Sites.baseChangeCompIso_inv_restriction` gives the hypothesis
`AlgebraicGeometry.Stack.LiftedSectionsCocycle` which
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean`
carries, with no further compatibility. -/
theorem liftedSectionsCocycle_at_belowArrowSite
    (hf4 : LiftedSectionsFactorFourSquareStandIn B E h S hS p hp) {x : 𝒳}
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F, hMx⟩)
    {z' z : 𝒳} (ψ : z' ⟶ z) (φ : z ⟶ x) (φ' : z' ⟶ x) (hφ' : φ' = ψ ≫ φ)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F))
    (hiso' : IsIso (restrictModulePullbackComparison B E h S hS p hp φ' (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    F.presheaf.map ψ.op ≫
        (liftedSectionsIso B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso').hom =
      (liftedSectionsIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
          (belowArrowSite B S hS p ψ φ φ' hφ').op := by
  let := h𝓕
  have hkg : B.inclusion.map (p.map φ').left =
      B.inclusion.map (p.map ψ).left ≫ B.inclusion.map (p.map φ).left := by
    rw [hφ', p.map_comp]
    exact B.inclusion.map_comp _ _
  obtain ⟨e, he, hfac⟩ := liftedSectionsIso_hom_eq B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso
  obtain ⟨e', he', hfac'⟩ := liftedSectionsIso_hom_eq B E h S hS p hp F hlqc φ' 𝓕 h𝓕 hMx eU hiso'
  have hmm : (overPostSectionsPresheaf B S hS p x 𝓕 h𝓕).map
        (belowArrowSite B S hS p ψ φ φ' hφ').op =
      (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
        (belowArrow B S hS p ψ φ φ' hkg).op := rfl
  rw [hfac, hfac', hmm]
  subst hφ'
  have hA := hf4 F hlqc 𝓕 h𝓕 hMx eU ψ φ hkg hiso hiso'
    (finalBaseChangeArrow B E h S hS p ψ)
  have hB := Stacks.Sites.baseChangeCompIso_inv_restriction_of_eq 𝓕
    (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map ψ).left)
    (B.inclusion.map (p.map (ψ ≫ φ)).left) hkg
    (A := (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      (smallEtaleFinal B E h S hS p z))
    (A' := (SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
      (smallEtaleFinal B E h S hS p z'))
    (finalBaseChangeArrow B E h S hS p ψ) e e'
    (belowArrow B S hS p ψ φ (ψ ≫ φ) hkg)
    (by rw [he, he']; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hC : (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
        (belowArrow B S hS p ψ φ (ψ ≫ φ) hkg ≫ e).op =
      (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map e.op ≫
        (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
          (belowArrow B S hS p ψ φ (ψ ≫ φ) hkg).op := by
    exact Functor.map_comp _ _ _
  exact paste_squares _ _ _ _ _ _ _ _ _ _ hA hB hC (Iso.inv_hom_id_app _ _)

/-- **The cocycle condition for `AlgebraicGeometry.Stack.liftedSectionsIso`, over the factor-4
stand-in.** -/
theorem liftedSectionsCocycle_of_factorFourSquare
    (hf4 : LiftedSectionsFactorFourSquareStandIn B E h S hS p hp) :
    LiftedSectionsCocycle B E h S hS p hp := by
  intro F hlqc x 𝓕 h𝓕 hMx eU z' z ψ φ φ' hφ' hiso hiso'
  exact liftedSectionsCocycle_at_belowArrowSite B E h S hS p hp F hlqc hf4 𝓕 h𝓕 hMx eU ψ φ φ'
    hφ' hiso hiso'

end AlgebraicGeometry.Stack

end
