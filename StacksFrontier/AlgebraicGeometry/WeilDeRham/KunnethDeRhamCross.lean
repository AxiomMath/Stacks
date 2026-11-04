module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethWedgeChain
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethCupPairing

/-!
# The de Rham Künneth map on cohomology is `x ⊗ y ↦ p^*x ∪ q^*y`

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y` with projections `p` and
`q`, and `A = Γ(S, 𝒪_S)`. The de Rham Künneth map of [Stacks, Tag 0FMB]

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(W, Ω^•_{W/S})`

(`Stacks.Cohomology.BoxKunneth.deRhamGlobalKunnethMap`), formed with the global cup product of
[Stacks, Section 0FKU] on the base, sends the tensor product of two de Rham classes to the cup
product of their pullbacks, when `A` is a field. The classes are read in relative de Rham
cohomology `AlgebraicGeometry.SheafOfModules.deRhamCohomology`, the pullbacks are the pullbacks of
[Stacks, Section 0FL6] (`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback`) read through the
comparison of the two realizations, and the cup product is
`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup`.

## Main definitions

* `Stacks.WeilDeRham.deRhamClassIso`: the cohomology of `RΓ(X, Ω^•_{X/S})` over the base is
  relative de Rham cohomology with its scalars restricted to `A`.
* `Stacks.WeilDeRham.deRhamPull`: the pullback of de Rham cohomology along a commutative square,
  read in the realization in which the cup product lives.

## Main results

* `Stacks.WeilDeRham.deRhamGlobalKunnethMap_crossProduct`: **the de Rham Künneth map on cohomology
  is `x ⊗ y ↦ p^*x ∪ q^*y`.**

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.BoxKunneth
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.DerivedTensor.RingedSite AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open scoped CategoryTheory.Prod TensorProduct

universe u


namespace Stacks.WeilDeRham

section Naturality

variable {S V : RingedSpace.{u, u}} (c : V ⟶ S)

/-- `sectionsOverBaseHomologyLerayIso` is natural in the complex. -/
theorem sectionsOverBaseHomologyLerayIso_naturality
    {T T' : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing V))} (g : T ⟶ T') (n : ℤ)
    (z : letI := @HasDerivedCategory.standard.{u, u + 1};
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
      ((sectionsOverBase c).obj T)) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (sectionsOverBaseHomologyLerayIso c T' n).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
          ((sectionsOverBase c).map g)).hom z) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n).map
          ((baseSections V).map g)).hom ((sectionsOverBaseHomologyLerayIso c T n).hom z) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have hl : ((lerayIso c).inv.app T ≫ (baseSections S).map ((derivedPushforward c).map g)) =
      (sectionsOverBase c).map g ≫ (lerayIso c).inv.app T' :=
    ((lerayIso c).inv.naturality g).symm
  have h₁ := (Stacks.Cohomology.HomologyPullback.map_map_comp_apply (𝟭 _)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n)
    ((sectionsOverBase c).map g) ((lerayIso c).inv.app T') z).symm.trans
    ((congrArg (fun t => ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
      t).hom z) hl.symm).trans
      (Stacks.Cohomology.HomologyPullback.map_map_comp_apply (𝟭 _)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n)
        ((lerayIso c).inv.app T) ((baseSections S).map ((derivedPushforward c).map g)) z))
  exact (congrArg (lerayCohomologyIso c T' n).hom h₁).trans
    (lerayCohomologyIso_naturality_apply c g n _)

end Naturality

section DeRham

/-- A module-valued functor applied after a functor, on an isomorphism and its inverse. -/
theorem map_inv_hom_apply {C D : Type*} [Category* C] [Category* D] {R : Type u} [Ring R]
    (F : C ⥤ D) (H : D ⥤ ModuleCat.{u} R) {c c' : C} (e : c ≅ c') (z : H.obj (F.obj c')) :
    (H.map (F.map e.hom)).hom ((H.map (F.map e.inv)).hom z) = z := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, ModuleCat.id_apply]

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The cohomology of `RΓ(X, Ω^•_{X/S})` over the base is relative de Rham cohomology**, with
its scalars restricted along `Γ(S, 𝒪_S) ⟶ Γ(X, a^{-1}𝒪_S)`: the Leray identification, followed by
the identification of the complex of `a^{-1}𝒪_S`-modules underlying the de Rham complex of
differential operators with the de Rham complex. -/
def deRhamClassIso (c : X ⟶ S) (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) n).obj
        ((sectionsOverBase (inverseImageBaseProjection c)).obj
          (DerivedCategory.Q.obj (leftComplex c (Scheme.Hom.deRhamDiffOpCochainComplex c)))) ≅
      (restrictGlobal (inverseImageBaseProjection c)).obj
        (cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex c)) n) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  sectionsOverBaseHomologyLerayIso (inverseImageBaseProjection c) _ n ≪≫
    (restrictGlobal (inverseImageBaseProjection c)).mapIso
      ((DerivedCategory.homologyFunctor _ n).mapIso ((baseSections (inverseImageBase c)).mapIso
        (DerivedCategory.Q.mapIso (leftComplexDeRhamIso c))))

/-- **The pullback of de Rham cohomology** along a commutative square `g' ≫ f = f' ≫ g`, read in
the realization by derived global sections of modules in which the cup product lives: the
pullback of [Stacks, Section 0FL6] conjugated by the comparison of the two realizations. -/
def deRhamPull {X' S' X'' S'' : Scheme.{u}} (g' : X' ⟶ X'') (f : X'' ⟶ S'') (f' : X' ⟶ S')
    (g : S' ⟶ S'') (w : g' ≫ f = f' ≫ g) (m : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f')) m :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f')
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
      m).hom.hom
    ((Scheme.Hom.deRhamCohomologyPullback g' f f' g w m).hom
      ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
        m).inv.hom x))

/-- The pullback of a class along a comparison `φ : M ≅ Ω^•_{X/S}` followed by the comparison of
derived and de Rham pullback is the de Rham pullback. -/
private theorem homologyPullback_comp_pullbackFormsOfEq {X X' S S' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g)
    (h : inverseImageBase f' ⟶ inverseImageBase f) (e : inverseImageBaseMap g' f' f g w = h)
    (m : ℤ)
    {M : letI := @HasDerivedCategory.standard.{u, u + 1};
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f)))}
    (φ : M ≅ letI := @HasDerivedCategory.standard.{u, u + 1};
      DerivedCategory.Q.obj (deRhamCochainComplex f))
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f'))) m).map
        ((baseSections (inverseImageBase f')).map
          ((derivedPullback h).map φ.hom ≫ pullbackFormsOfEq g' f' f g w h e))).hom
      (Stacks.Cohomology.HomologyPullback.homologyPullback h M m
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) m).map
          ((baseSections (inverseImageBase f)).map φ.inv)).hom x)) =
      deRhamPull g' f f' g w m x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have h₁ := Stacks.Cohomology.HomologyPullback.homologyPullback_naturality h φ.hom m
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) m).map
      ((baseSections (inverseImageBase f)).map φ.inv)).hom x)
  have h₂ := map_inv_hom_apply (baseSections (inverseImageBase f))
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) m) φ x
  have h₃ := deRhamCohomologyPullback_eq_homologyPullback_ofEq g' f' f g w h e m
    ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
      m).inv.hom x)
  have h₄ := congrArg (fun t => ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing
      (inverseImageBase f'))) m).map
      ((baseSections (inverseImageBase f')).map (pullbackFormsOfEq g' f' f g w h e))).hom
      (Stacks.Cohomology.HomologyPullback.homologyPullback h
        (DerivedCategory.Q.obj (deRhamComplexInt f)) m t))
    ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
      m).inv_hom_id_apply x)
  refine (Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _).trans ?_
  refine (congrArg _ ((congrArg (Stacks.Cohomology.HomologyPullback.homologyPullback h
    (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) h₂).symm.trans h₁).symm).trans ?_
  exact (h₃.trans h₄).symm

/-- **The comparison along the first projection carries the pullback of classes to the de Rham
pullback.** -/
theorem homologyPullback_fstFormsQ (i : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex a)) i) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing
        (inverseImageBase (pullback.fst a b ≫ a)))) i).map
        ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map (fstFormsQ a b))).hom
      (Stacks.Cohomology.HomologyPullback.homologyPullback (fstProjection a b)
        (DerivedCategory.Q.obj (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a))) i
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase a))) i).map
          ((baseSections (inverseImageBase a)).map
            (DerivedCategory.Q.map (leftComplexDeRhamIso a).inv))).hom x)) =
      deRhamPull (pullback.fst a b) a (pullback.fst a b ≫ a) (𝟙 S) (fst_comp_eq a b) i x :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  homologyPullback_comp_pullbackFormsOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S)
    (fst_comp_eq a b) (fstProjection a b)
    (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))
    i (DerivedCategory.Q.mapIso (leftComplexDeRhamIso a)) x

/-- **The comparison along the second projection carries the pullback of classes to the de Rham
pullback.** -/
theorem homologyPullback_sndFormsQ (j : ℤ)
    (y : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex b)) j) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing
        (inverseImageBase (pullback.fst a b ≫ a)))) j).map
        ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map (sndFormsQ a b))).hom
      (Stacks.Cohomology.HomologyPullback.homologyPullback (sndProjection a b)
        (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))) j
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase b))) j).map
          ((baseSections (inverseImageBase b)).map
            (DerivedCategory.Q.map (leftComplexDeRhamIso b).inv))).hom y)) =
      deRhamPull (pullback.snd a b) b (pullback.fst a b ≫ a) (𝟙 S) (snd_comp_eq a b) j y :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  homologyPullback_comp_pullbackFormsOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S)
    (snd_comp_eq a b) (sndProjection a b)
    (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))
    j (DerivedCategory.Q.mapIso (leftComplexDeRhamIso b)) y

/-- A threefold composite equal to a morphism `r`, on cohomology of derived global sections. -/
theorem homology_map_comp₃_of_eq {V : RingedSpace.{u, u}}
    {A B C D : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing V))}
    (u₁ : A ⟶ B) (u₂ : B ⟶ C) (u₃ : C ⟶ D) (r : A ⟶ D) (h : u₁ ≫ u₂ ≫ u₃ = r) (n : ℤ)
    (z : letI := @HasDerivedCategory.standard.{u, u + 1}; cohomologyModule A n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n).map
        ((baseSections V).map u₃)).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n).map
        ((baseSections V).map u₂)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n).map
          ((baseSections V).map u₁)).hom z)) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n).map
        ((baseSections V).map r)).hom z := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst h
  exact ((Stacks.Cohomology.HomologyPullback.map_map_comp_apply (baseSections V)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n) u₁ (u₂ ≫ u₃) z).trans
    (Stacks.Cohomology.HomologyPullback.map_map_comp_apply (baseSections V)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing V)) n) u₂ u₃ _)).symm

/-- A module-valued functor on a threefold composite, on an element. -/
theorem map_comp₃_apply {C : Type*} [Category* C] {R : Type u} [Ring R] (H : C ⥤ ModuleCat.{u} R)
    {x₀ x₁ x₂ x₃ : C} (u₁ : x₀ ⟶ x₁) (u₂ : x₁ ⟶ x₂) (u₃ : x₂ ⟶ x₃) (z : H.obj x₀) :
    (H.map ((u₁ ≫ u₂) ≫ u₃)).hom z = (H.map u₃).hom ((H.map u₂).hom ((H.map u₁).hom z)) := by
  simp only [Functor.map_comp, ModuleCat.comp_apply]

/-- **The de Rham Künneth map on cohomology is `x ⊗ y ↦ p^*x ∪ q^*y`**, when `Γ(S, 𝒪_S)` is a
field: the map of [Stacks, Tag 0FMB], built from the global cup product of
[Stacks, Section 0FKU] on the base, carries the cohomology product of [Stacks, Tag 068H] of two
de Rham classes to the cup product of their pullbacks along the two projections. -/
theorem deRhamGlobalKunnethMap_crossProduct (hS : IsField (baseRing S.toRingedSpace)) (i j : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex a)) i)
    (y : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex b)) j) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (deRhamClassIso (pullback.fst a b ≫ a) (i + j)).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).map
        (deRhamGlobalKunnethMap a b (cupProductOnSpace S.toRingedSpace))).hom
        ((crossProductCast _ _ i j (i + j) rfl).hom
          ((deRhamClassIso a i).inv x ⊗ₜ (deRhamClassIso b j).inv y))) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup
        (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))) i j
        (deRhamPull (pullback.fst a b) a (pullback.fst a b ≫ a) (𝟙 S) (fst_comp_eq a b) i x)
        (deRhamPull (pullback.snd a b) b (pullback.fst a b ≫ a) (𝟙 S) (snd_comp_eq a b) j y) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  -- the two classes, read on the complexes the Künneth maps are formed on
  have hcore := kunnethGlobalMap_crossProduct (inverseImageBaseProjection a)
    (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
    (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
    (sndProjection_comp a b) hS
    (DerivedCategory.Q.obj (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)))
    (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))) i j
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase a))) i).map
      ((baseSections (inverseImageBase a)).map
        (DerivedCategory.Q.map (leftComplexDeRhamIso a).inv))).hom x)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase b))) j).map
      ((baseSections (inverseImageBase b)).map
        (DerivedCategory.Q.map (leftComplexDeRhamIso b).inv))).hom y)
  have hbox := homology_map_comp₃_of_eq _ _ _ _
    (boxTotalDerivedComparison_deRhamBoxTotalKunnethIso a b) (i + j)
    ((cupPairing (cupProductOnSpace (inverseImageBase (pullback.fst a b ≫ a)))
      ((derivedPullback (fstProjection a b)).obj
        (DerivedCategory.Q.obj (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a))))
      ((derivedPullback (sndProjection a b)).obj
        (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))))
        i j).hom
      (Stacks.Cohomology.HomologyPullback.homologyPullback (fstProjection a b) _ i
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase a))) i).map
          ((baseSections (inverseImageBase a)).map
            (DerivedCategory.Q.map (leftComplexDeRhamIso a).inv))).hom x) ⊗ₜ
        Stacks.Cohomology.HomologyPullback.homologyPullback (sndProjection a b) _ j
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase b))) j).map
          ((baseSections (inverseImageBase b)).map
            (DerivedCategory.Q.map (leftComplexDeRhamIso b).inv))).hom y)))
  have hnat := cupPairing_naturality_apply
    (cupProductOnSpace (inverseImageBase (pullback.fst a b ≫ a))) (fstFormsQ a b) (sndFormsQ a b)
    i j
    (Stacks.Cohomology.HomologyPullback.homologyPullback (fstProjection a b) _ i
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase a))) i).map
          ((baseSections (inverseImageBase a)).map
            (DerivedCategory.Q.map (leftComplexDeRhamIso a).inv))).hom x))
    (Stacks.Cohomology.HomologyPullback.homologyPullback (sndProjection a b) _ j
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase b))) j).map
          ((baseSections (inverseImageBase b)).map
            (DerivedCategory.Q.map (leftComplexDeRhamIso b).inv))).hom y))
  have hs₁ := sectionsOverBaseHomologyLerayIso_naturality
    (inverseImageBaseProjection (pullback.fst a b ≫ a))
    (DerivedCategory.Q.map (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom)) (i + j)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).map
      ((sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalDerivedComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
        (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0
        (boxTotalComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
          (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0)))).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).map
        (kunnethGlobalMap (inverseImageBaseProjection a)
        (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
        (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
        (sndProjection_comp a b) (cupProductOnSpace S.toRingedSpace)
        (DerivedCategory.Q.obj (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)))
        (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))))).hom
        ((crossProductCast _ _ i j (i + j) rfl).hom
          ((deRhamClassIso a i).inv x ⊗ₜ (deRhamClassIso b j).inv y))))
  have hs₂ := sectionsOverBaseHomologyLerayIso_naturality
    (inverseImageBaseProjection (pullback.fst a b ≫ a))
    (boxTotalDerivedComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
        (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0
        (boxTotalComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
          (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0)) (i + j)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).map
        (kunnethGlobalMap (inverseImageBaseProjection a)
        (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
        (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
        (sndProjection_comp a b) (cupProductOnSpace S.toRingedSpace)
        (DerivedCategory.Q.obj (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)))
        (DerivedCategory.Q.obj (rightComplex b (Scheme.Hom.deRhamDiffOpCochainComplex b))))).hom
        ((crossProductCast _ _ i j (i + j) rfl).hom
          ((deRhamClassIso a i).inv x ⊗ₜ (deRhamClassIso b j).inv y)))
  have hc := congrArg₂ (fun u v =>
    (cupPairing (cupProductOnSpace (inverseImageBase (pullback.fst a b ≫ a)))
      (DerivedCategory.Q.obj (deRhamCochainComplex (pullback.fst a b ≫ a)))
      (DerivedCategory.Q.obj (deRhamCochainComplex (pullback.fst a b ≫ a))) i j).hom (u ⊗ₜ v))
    (homologyPullback_fstFormsQ a b i x) (homologyPullback_sndFormsQ a b j y)
  refine (congrArg (fun t => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom))).hom
    ((sectionsOverBaseHomologyLerayIso (inverseImageBaseProjection (pullback.fst a b ≫ a)) _
      (i + j)).hom t))
    (map_comp₃_apply
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j))
      _ _ _ _)).trans ?_
  refine (congrArg (fun t => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom))).hom t)
    hs₁).trans ?_
  refine (congrArg (fun t => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom))).hom
    (((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom)))).hom t)) hs₂).trans ?_
  refine (congrArg (fun t => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map (leftComplexDeRhamIso (pullback.fst a b ≫ a)).hom))).hom
    (((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom)))).hom
      (((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase (pullback.fst a b ≫ a)))) (i + j)).map
      ((baseSections (inverseImageBase (pullback.fst a b ≫ a))).map
        (boxTotalDerivedComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
          (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0
          (boxTotalComparison a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
            (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0)))).hom t))) hcore).trans ?_
  refine hbox.trans ?_
  refine (Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _).trans ?_
  refine (congrArg _ hnat.symm).trans ?_
  refine (congrArg _ hc).trans ?_
  exact (ModuleCat.comp_apply _ _ _).symm

end DeRham

end Stacks.WeilDeRham

end
