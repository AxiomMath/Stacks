module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of étale sheaves to the Zariski site

An open immersion is étale, so the lattice `S.Opens` of open subschemes of a scheme `S` sits
inside the small étale site of `S`. Restricting an étale sheaf along that inclusion and
sheafifying for the Zariski topology produces the *Zariski restriction* `ε_* F` of the sheaf,
the direct image along the morphism of sites `ε : S_ét ⟶ S_Zar` of Stacks 09AX.

The direct-image functor is defined both for Mathlib's small étale site `S.Etale` and for the
size-bounded small étale site `AlgebraicGeometry.SmallEtale B S hS`, and it is left exact.

The comparison map of constant integer sheaves sends an integer to the same section over every
open subscheme.

## Main definitions

* `AlgebraicGeometry.opensToEtale` — the open subschemes inside Mathlib's small étale site.
* `AlgebraicGeometry.zariskiRestrictionFunctor` — the direct image `ε_*` for that site.
* `AlgebraicGeometry.opensToBoundedEtale`, `AlgebraicGeometry.boundedZariskiRestrictionFunctor`
  — the same two constructions for the bounded small étale site.
* `AlgebraicGeometry.constantIntSheafRestrictionHom` and
  `AlgebraicGeometry.boundedConstantIntSheafRestrictionHom` — the canonical comparison of
  constant integer sheaves, obtained by sheafifying the restriction of the étale
  sheafification unit.

## Main results

* `AlgebraicGeometry.zariskiRestrictionFunctor_preservesFiniteLimits` and
  `AlgebraicGeometry.boundedZariskiRestrictionFunctor_preservesFiniteLimits` — the Zariski
  restriction is left exact.

## References

* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

section Mathlib

/-- The canonical inclusion of the open subschemes of `S` into its small étale site. -/
public def opensToEtale (S : Scheme.{u}) : S.Opens ⥤ S.Etale where
  obj U := .mk U.ι
  map {U V} f := MorphismProperty.Over.homMk (S.homOfLE f.le)
    (S.homOfLE_ι f.le)
  map_id U := by
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    change S.homOfLE (le_refl U) = 𝟙 _
    simp
  map_comp f g := MorphismProperty.Comma.Hom.ext'
    (Over.OverMorphism.ext (S.homOfLE_homOfLE f.le g.le).symm)

/-- The restriction of an étale abelian sheaf to the Zariski site: restrict its sections to
the open subschemes and sheafify. -/
public def zariskiRestriction (S : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v}) :
    Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v} :=
  (presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}).obj
    ((opensToEtale S).op ⋙ F.obj)

/-- Direct image from the small étale site to the Zariski site, i.e. `ε_*` for the morphism of
sites `ε : S_ét ⟶ S_Zar` given by the inclusion of the open subschemes. -/
public def zariskiRestrictionFunctor (S : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}] :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{v} ⥤
      Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v} :=
  sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{v} ⋙
    (Functor.whiskeringLeft _ _ _).obj (opensToEtale S).op ⋙
      presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}

/-- Restriction to the Zariski site is left exact. -/
public theorem zariskiRestrictionFunctor_preservesFiniteLimits
    (S : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}] :
    PreservesFiniteLimits (zariskiRestrictionFunctor.{u, v} S) := by
  unfold zariskiRestrictionFunctor
  infer_instance

/-- On presheaves, the étale sheafification unit restricts each integer to the same integer on
every open subscheme. -/
public def constantIntPresheafRestrictionMap (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}] :
    (Functor.const S.Opensᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      (opensToEtale S).op ⋙
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift ℤ))).obj where
  app U := (toSheafify S.smallEtaleTopology
    (((Functor.const S.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))) :
      S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v})).app
      ((opensToEtale S).op.obj U)
  naturality U V f := by
    simpa [constantSheaf, sheafify, presheafToSheaf] using
      (toSheafify S.smallEtaleTopology
        (((Functor.const S.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))) :
          S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v})).naturality
          ((opensToEtale S).op.map f)

/-- The canonical morphism between constant integer sheaves, obtained by sheafifying the
restriction of the étale sheafification unit. -/
public def constantIntSheafRestrictionHom (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}] :
    (constantSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
      (zariskiRestrictionFunctor S).obj
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift ℤ))) :=
  (presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}).map
    (constantIntPresheafRestrictionMap S)

end Mathlib

section Bounded

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical inclusion of the open subschemes of `S` into the size-bounded small étale
site `SmallEtale B S hS`. -/
public def opensToBoundedEtale : S.Opens ⥤ SmallEtale B S hS where
  obj U := by
    let hU : B.Contains U.toScheme :=
      Scheme.size_lt_of_isOpenImmersion U.ι hS
    exact ⟨Over.mk (X := B.obj S hS) (Y := B.obj U.toScheme hU)
      (ObjectProperty.homMk U.ι), show Etale U.ι from inferInstance⟩
  map {U V} f := by
    apply ObjectProperty.homMk
    refine Over.homMk (ObjectProperty.homMk (S.homOfLE f.le)) ?_
    apply ObjectProperty.hom_ext
    exact S.homOfLE_ι f.le
  map_id U := by
    ext
    change S.homOfLE (le_refl U) = 𝟙 _
    simp
  map_comp f g := by
    ext
    exact (S.homOfLE_homOfLE f.le g.le).symm

/-- Direct image from the bounded small étale site to the Zariski site. -/
public def boundedZariskiRestrictionFunctor
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}] :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v} ⥤
      Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v} :=
  sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v} ⋙
    (Functor.whiskeringLeft _ _ _).obj (opensToBoundedEtale B S hS).op ⋙
      presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}

/-- Restriction from the bounded small étale site to the Zariski site is left exact. -/
public theorem boundedZariskiRestrictionFunctor_preservesFiniteLimits
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}] :
    PreservesFiniteLimits (boundedZariskiRestrictionFunctor.{u, v} B S hS) := by
  unfold boundedZariskiRestrictionFunctor
  infer_instance

/-- The étale sheafification unit on the bounded small étale site sends an integer to the same
section over every open subscheme. -/
public def boundedConstantIntPresheafRestrictionMap
    [HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{v}] :
    (Functor.const S.Opensᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      (opensToBoundedEtale B S hS).op ⋙
        ((constantSheaf (SmallEtale.topology B S hS)
          AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))).obj where
  app U := (toSheafify (SmallEtale.topology B S hS)
    (((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))) :
      (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{v})).app
        ((opensToBoundedEtale B S hS).op.obj U)
  naturality U V f := by
    simpa [constantSheaf, sheafify, presheafToSheaf] using
      (toSheafify (SmallEtale.topology B S hS)
        (((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))) :
          (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{v})).naturality
            ((opensToBoundedEtale B S hS).op.map f)

/-- The canonical morphism of constant integer sheaves for the bounded small étale site. -/
public def boundedConstantIntSheafRestrictionHom
    [HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{v}]
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{v}] :
    (constantSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶
      (boundedZariskiRestrictionFunctor B S hS).obj
        ((constantSheaf (SmallEtale.topology B S hS)
          AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))) :=
  (presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{v}).map
    (boundedConstantIntPresheafRestrictionMap B S hS)

end Bounded

end AlgebraicGeometry
