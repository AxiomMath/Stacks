module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Modules on a one-point ringed space, and pullback to the spectrum

For a commutative ring `R` let `({*}, R)` be the ringed space with one point and ring `R`.
Pulling an `R`-module back along the canonical morphism `π : Spec R ⟶ ({*}, R)` gives its
associated module sheaf, so the `tilde` construction is a pullback.

## Main definitions

* `AlgebraicGeometry.affinePointMorphism` is the canonical morphism `Spec R ⟶ ({*}, R)`, induced
  by the inverse of the canonical global-sections isomorphism of `Spec R`.
* `AlgebraicGeometry.affinePointModuleFunctor` regards an `R`-module as a module sheaf on
  `({*}, R)`.

## Main results

* `AlgebraicGeometry.affinePointPullbackIsoTilde` is the natural isomorphism `π^* M ≅ M̃`,
  simultaneously for all `R`-modules `M`.

## Implementation notes

The one-point ringed space itself, the morphisms into it, the functor regarding an `R`-module as
a module sheaf on it, and the global-sections functor in the other direction all already exist in
`Stacks.AssociatedSheaf`, where they are `coefficientPoint`, `toCoefficientPoint`,
`associatedSheafFunctor` and `globalSectionsFunctor`. They are used here rather than rebuilt: only
the morphism out of `Spec R` and the comparison with `tilde` are new.

The comparison is obtained by identifying both functors as left adjoints of the same right
adjoint — the global-sections functor of the point composed with pushforward — and then appealing
to uniqueness of adjoints, so it does not depend on the `tilde` construction's definition. The
only computation involved is that the two scalar maps `R → Γ(Spec R, 𝒪)` agree, which is
`Stacks.AssociatedSheaf.structureSheafHom_app_top_apply`.

## References

* [Stacks Project, Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace TopCat Opposite Stacks.AssociatedSheaf

universe u

namespace AlgebraicGeometry

/-- The canonical morphism `Spec R ⟶ ({*}, R)`, induced by the inverse of the canonical
global-sections isomorphism. -/
public noncomputable abbrev affinePointMorphism (R : CommRingCat.{u}) :
    (Spec R).toLocallyRingedSpace.toRingedSpace ⟶ coefficientPoint (CommRingCat.of ↑R) :=
  toCoefficientPoint' _ (Scheme.ΓSpecIso R).inv.hom

/-- The functor regarding an `R`-module as a module sheaf on `({*}, R)`: the associated-sheaf
construction on the one-point space, for the canonical identification of `R` with the sections
of the point's structure sheaf. -/
public noncomputable abbrev affinePointModuleFunctor (R : CommRingCat.{u}) :
    ModuleCat.{u} ↑R ⥤
      SheafOfModules.{u} (structureSheafRing
        (coefficientPoint (CommRingCat.of ↑R))) :=
  associatedSheafFunctor.{u, u} (coefficientPoint (CommRingCat.of ↑R))
    (coefficientPointSectionsIso (CommRingCat.of ↑R)).hom.hom

/-- Global sections on the one-point ringed space, read as an `R`-module: the right adjoint of
`AlgebraicGeometry.affinePointModuleFunctor`. -/
private noncomputable abbrev pointSections (R : CommRingCat.{u}) :
    SheafOfModules.{u} (structureSheafRing
      (coefficientPoint (CommRingCat.of ↑R))) ⥤ ModuleCat.{u} ↑R :=
  globalSectionsFunctor.{u, u} (coefficientPoint (CommRingCat.of ↑R))
    (coefficientPointSectionsIso (CommRingCat.of ↑R)).hom.hom

private noncomputable def pointModuleAdjunction (R : CommRingCat.{u}) :
    affinePointModuleFunctor R ⊣ pointSections R :=
  associatedSheafAdjunction.{u, u} (coefficientPoint (CommRingCat.of ↑R))
    (coefficientPointSectionsIso (CommRingCat.of ↑R)).hom.hom

/-- Global sections on the point of the pushforward along `π` is the global-sections functor of
`Spec R`. Both send a module sheaf `M` to `Γ(Spec R, M)`; the two `R`-module structures are
restrictions along two ring maps `R → Γ(Spec R, 𝒪)` which agree by
`Stacks.AssociatedSheaf.structureSheafHom_app_top_apply`, so the underlying additive equivalence
is the identity. -/
private noncomputable def pushforwardPointSectionsIso (R : CommRingCat.{u}) :
    RingedSpaceModuleAdjunction.modulePushforward (affinePointMorphism R) ⋙
      pointSections R ≅ moduleSpecΓFunctor := by
  -- The two `Module` instances are passed explicitly. They are regular implicit arguments of
  -- `LinearEquiv.toModuleIso`, so leaving them to be synthesized asks instance search to
  -- identify `↑R` with the scalars of the point's constant ring presheaf at `⊤`, which is a
  -- `delta` step and therefore unavailable at reducible transparency.
  refine NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso (R := ↑R)
    (X₁ := ↑((RingedSpaceModuleAdjunction.modulePushforward (affinePointMorphism R) ⋙
      pointSections R).obj M))
    (X₂ := ↑(moduleSpecΓFunctor.obj M))
    (m₁ := ModuleCat.isModule _) (m₂ := ModuleCat.isModule _)
    { __ := AddEquiv.refl _
      map_smul' := ?_ }) ?_
  · intro r m
    refine congrArg (fun s : ↑((structureSheafRing
        (Spec R).toLocallyRingedSpace.toRingedSpace).obj.obj (op ⊤)) ↦
      s • (show M.val.obj (op ⊤) from m)) ?_
    -- `(whiskerRight θ F).app U = F.map (θ.app U)` holds by `rfl` but is not a `simp` lemma, so
    -- `globalSectionsMap_app_top_apply` cannot be rewritten with until the scalar map is spelled
    -- without the whiskering. `change` elaborates at default transparency and does that.
    change ((RingedSpaceModuleAdjunction.structureSheafHom (affinePointMorphism R)).hom.app
          (op ⊤)).hom
        (((globalSectionsMap (coefficientPoint (CommRingCat.of ↑R))
            (CommRingCat.Hom.hom (coefficientPointSectionsIso (CommRingCat.of ↑R)).hom)).app
          (op ⊤)).hom r) = _
    rw [globalSectionsMap_app_top_apply]
    refine (structureSheafHom_app_top_apply (Spec R).toLocallyRingedSpace.toRingedSpace
      (Scheme.ΓSpecIso R).inv.hom r).trans ?_
    rfl
  · intro M N f
    ext m
    rfl

/-- The comparison isomorphism of `AlgebraicGeometry.affinePointPullbackIsoTilde` exists.

Stated as a `Nonempty` because it comes from uniqueness of left adjoints, which determines the
isomorphism only up to the choice of adjoint. -/
public lemma affinePointPullbackIsoTilde_nonempty (R : CommRingCat.{u}) :
    Nonempty (affinePointModuleFunctor R ⋙
      RingedSpaceModuleAdjunction.modulePullback (affinePointMorphism R) ≅
        tilde.functor R) :=
  ⟨Adjunction.leftAdjointUniq
    (((pointModuleAdjunction R).comp
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        (affinePointMorphism R))).ofNatIsoRight (pushforwardPointSectionsIso R))
    tilde.adjunction⟩

/-- Pullback along the canonical morphism `Spec R ⟶ ({*}, R)` is naturally isomorphic to the
associated module sheaf functor, so `tilde` is a pullback. -/
public noncomputable def affinePointPullbackIsoTilde (R : CommRingCat.{u}) :
    affinePointModuleFunctor R ⋙
        RingedSpaceModuleAdjunction.modulePullback (affinePointMorphism R) ≅
      tilde.functor R :=
  Classical.choice (affinePointPullbackIsoTilde_nonempty R)

end AlgebraicGeometry
