module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex.HomComplexColimit
import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# Local cohomology of a normalized dualizing complex

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, and let
`Z = V(𝔪)` be the closed point of `Spec(A)`. Then `RΓ_Z(ω)` is concentrated in degree zero,
where it is an injective hull of `κ`.

## Main results

* `Dualizing.LocalDuality.exists_isInjectiveHull_homology_zero_localCohomology`: the
  degree-zero local cohomology `R⁰Γ_Z(ω)` is an injective hull of the residue field.
* `Dualizing.LocalDuality.nonempty_localCohomology_iso_single_homology_zero`: local cohomology
  `RΓ_Z(ω)` is its degree-zero cohomology module placed in degree zero.

This file also compares the derived Hom models over `A` and over `ULift A`, and was split from
`StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex`.

## References

* [Stacks Project, Tag 0A82](https://stacks.math.columbia.edu/tag/0A82)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing.LocalDuality

open CochainComplex.HomComplex StacksDraft.DerivedHom

universe u v w

/-- Every module over a local ring, in particular the universe-lifted residue field, admits an
injective hull. -/
private theorem exists_residueFieldInjectiveHull
    (A : Type u) [CommRing A] [IsLocalRing A] :
    ∃ (E : ModuleCat.{max v u} A)
      (i : (ModuleCat.uliftFunctor.{v} A).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
      (hi : Mono i),
      @Module.IsInjectiveHull (ModuleCat.{max v u} A) _ _ _ _ _ i hi :=
  Module.exists_isInjectiveHull A
    ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A (IsLocalRing.ResidueField A)))

/-- Restriction of scalars along `ULift.ringEquiv` preserves K-injectivity of complexes. -/
private theorem liftedComplex_isKInjective (A : Type u) [CommRing A]
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((uliftModuleEquivalence.{u, max v u, v} A).inverse.mapHomologicalComplex
        (.up ℤ)).obj J) := by
  let e := uliftModuleEquivalence.{u, max v u, v} A
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    e.inverse e.functor e.toAdjunction J

/-- A fully faithful additive functor induces a bijection on cochains. -/
private theorem cochainMapBijective
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (K L : CochainComplex C ℤ) (q : ℤ) :
    Function.Bijective (fun z : Cochain K L q => z.map F) := by
  refine ⟨fun x y h ↦ ?_, fun z ↦ ⟨Cochain.mk fun p r hpr ↦ F.preimage (z.v p r hpr), ?_⟩⟩
  · ext p r hpr
    exact F.map_injective (congrArg (fun z : Cochain _ _ q ↦ z.v p r hpr) h)
  · ext p r hpr
    exact F.map_preimage _

/-- Restriction of scalars along `ULift.ringEquiv` commutes with the Hom complex. -/
private noncomputable def scalarHomComplexMap (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) :
    (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.HomComplexR (ULift.{v} A) K L)) ⟶
      CochainComplex.HomComplexR A
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj K)
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex
          (.up ℤ)).obj L) where
  f q := ModuleCat.ofHom (X := ((uliftModuleEquivalence.{u, max v u, v} A).functor.obj
    ((CochainComplex.HomComplexR (ULift.{v} A) K L).X q))) {
    toFun := fun z ↦ z.map (uliftModuleEquivalence.{u, max v u, v} A).functor
    map_add' := fun x y ↦ Cochain.map_add x y _
    map_smul' := by
      intro r z
      apply Cochain.ext
      intro p s hps
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl }
  comm' q r _ := by
    ext z : 2
    exact CochainComplex.HomComplex.δ_map q r z
      (uliftModuleEquivalence.{u, max v u, v} A).functor

/-- The comparison of Hom complexes is compatible with precomposition. -/
private theorem scalarHomComplexMap_precomp (A : Type u) [CommRing A]
    {K K' L : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ}
    (f : K' ⟶ K) :
    (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).map
      (Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} A) K' K L f)) ≫
      scalarHomComplexMap A K' L =
    scalarHomComplexMap A K L ≫
      Stacks.HomComplex.TensorHomMap.precomp A _ _ _
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex
          (.up ℤ)).map f) := by
  ext q : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  show ((Cochain.ofHom f).comp z (zero_add q)).map
      (uliftModuleEquivalence.{u, max v u, v} A).functor = _
  exact (Cochain.map_comp _ (Cochain.ofHom f) z (zero_add q)
      (uliftModuleEquivalence.{u, max v u, v} A).functor).trans
    (congrArg (fun w ↦ Cochain.comp w
        (z.map (uliftModuleEquivalence.{u, max v u, v} A).functor) (zero_add q))
      (Cochain.map_ofHom _ _ f (uliftModuleEquivalence.{u, max v u, v} A).functor))

/-- The comparison of Hom complexes is an isomorphism. -/
private theorem scalarHomComplexMap_isIso (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) :
    IsIso (scalarHomComplexMap A K L) := by
  let : ∀ q : ℤ, IsIso ((scalarHomComplexMap A K L).f q) := fun q ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := uliftModuleEquivalence.{u, max v u, v} A
    have : e.functor.IsEquivalence := e.isEquivalence_functor
    exact cochainMapBijective e.functor K L q
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Restriction of scalars commutes with the localization functor to the derived category. -/
private noncomputable def scalarDerivedFactorsApp (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) :
    (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex
          (.up ℤ)).obj C) :=
  ((uliftModuleEquivalence.{u, max v u, v} A).functor.mapDerivedCategoryFactors).app C

/-- The comparison of derived images is natural in the complex. -/
private theorem scalarDerivedFactorsApp_naturality (A : Type u) [CommRing A]
    {C C' : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ} (φ : C ⟶ C') :
    (derivedScalarEquivalence.{u, v} A).functor.map (DerivedCategory.Q.map φ) ≫
        (scalarDerivedFactorsApp A C').hom =
      (scalarDerivedFactorsApp A C).hom ≫
        DerivedCategory.Q.map
          (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex
            (.up ℤ)).map φ) :=
  ((uliftModuleEquivalence.{u, max v u, v} A).functor.mapDerivedCategoryFactors).hom.naturality φ

/-- The counit of the restriction-of-scalars equivalence on complexes. -/
private noncomputable def complexCounitIso (A : Type u) [CommRing A]
    (L : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj
      (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
        (.up ℤ)).inverse.obj L)) ≅ L :=
  ((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex (.up ℤ)).counitIso.app L

/-- The counit of the restriction-of-scalars equivalence, read in the derived category. -/
private noncomputable def derivedCounitIso (A : Type u) [CommRing A]
    (L : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ((derivedScalarEquivalence.{u, v} A).functor.obj
      (DerivedCategory.Q.obj
        (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
          (.up ℤ)).inverse.obj L))) ≅
      DerivedCategory.Q.obj L :=
  scalarDerivedFactorsApp A
      (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
        (.up ℤ)).inverse.obj L) ≪≫
    DerivedCategory.Q.mapIso (complexCounitIso A L)

/-- The counit of the restriction-of-scalars equivalence, read on Hom complexes. -/
private noncomputable def homComplexCounitIso (A : Type u) [CommRing A]
    (K L : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    CochainComplex.HomComplexR A
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj
          (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
            (.up ℤ)).inverse.obj K))
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj
          (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
            (.up ℤ)).inverse.obj L)) ≅
      CochainComplex.HomComplexR A K L := by
  let eK := complexCounitIso A K
  let eL := complexCounitIso A L
  let K0 := ((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj
    (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex (.up ℤ)).inverse.obj K)
  let L0 := ((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).obj
    (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex (.up ℤ)).inverse.obj L)
  let ePre : CochainComplex.HomComplexR A K0 L0 ≅
      CochainComplex.HomComplexR A K L0 := {
    hom := Stacks.HomComplex.TensorHomMap.precomp A K K0 L0 eK.inv
    inv := Stacks.HomComplex.TensorHomMap.precomp A K0 K L0 eK.hom
    hom_inv_id := by simp [← Stacks.HomComplex.TensorHomMap.precomp_comp]
    inv_hom_id := by simp [← Stacks.HomComplex.TensorHomMap.precomp_comp] }
  let ePost : CochainComplex.HomComplexR A K L0 ≅
      CochainComplex.HomComplexR A K L := {
    hom := Stacks.HomComplex.TensorHomMap.postcomp A K L0 L eL.hom
    inv := Stacks.HomComplex.TensorHomMap.postcomp A K L L0 eL.inv
    hom_inv_id := by simp [← Stacks.HomComplex.TensorHomMap.postcomp_comp]
    inv_hom_id := by simp [← Stacks.HomComplex.TensorHomMap.postcomp_comp] }
  exact ePre ≪≫ ePost

/-- Precomposition and postcomposition on Hom complexes commute. -/
private theorem highUniverse_precomp_postcomp (A : Type u) [CommRing A]
    {K K' L L' : CochainComplex (ModuleCat.{max v u} A) ℤ}
    (f : K' ⟶ K) (g : L ⟶ L') :
    Stacks.HomComplex.TensorHomMap.precomp A K' K L f ≫
        Stacks.HomComplex.TensorHomMap.postcomp A K' L L' g =
      Stacks.HomComplex.TensorHomMap.postcomp A K L L' g ≫
        Stacks.HomComplex.TensorHomMap.precomp A K' K L' f := by
  ext q : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  show ((Cochain.ofHom f).comp z (zero_add q)).comp
      (Cochain.ofHom g) (add_zero q) =
    (Cochain.ofHom f).comp (z.comp (Cochain.ofHom g) (add_zero q)) (zero_add q)
  exact Cochain.comp_assoc (Cochain.ofHom f) z (Cochain.ofHom g)
    (zero_add q) (add_zero q) (by omega)

/-- The counit comparison on Hom complexes is compatible with precomposition. -/
private theorem homComplexCounitIso_precomp (A : Type u) [CommRing A]
    {K K' L : CochainComplex (ModuleCat.{max v u} A) ℤ} (f : K' ⟶ K) :
    Stacks.HomComplex.TensorHomMap.precomp A _ _ _
        (((uliftModuleEquivalence.{u, max v u, v} A).functor.mapHomologicalComplex (.up ℤ)).map
          (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
            (.up ℤ)).inverse.map f)) ≫
      (homComplexCounitIso A K' L).hom =
    (homComplexCounitIso A K L).hom ≫ Stacks.HomComplex.TensorHomMap.precomp A K' K L f := by
  let ec := (uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex (.up ℤ)
  let eK := complexCounitIso A K
  let eK' := complexCounitIso A K'
  let eL := complexCounitIso A L
  have hn : eK'.inv ≫ ec.functor.map (ec.inverse.map f) = f ≫ eK.inv := by
    have h := ec.counitIso.inv.naturality f
    simpa [ec, eK, eK', complexCounitIso] using h.symm
  dsimp only [homComplexCounitIso, Iso.trans_hom]
  change
    Stacks.HomComplex.TensorHomMap.precomp A _ _ _ (ec.functor.map (ec.inverse.map f)) ≫
      Stacks.HomComplex.TensorHomMap.precomp A K' _ _ eK'.inv ≫
        Stacks.HomComplex.TensorHomMap.postcomp A K' _ L eL.hom =
    Stacks.HomComplex.TensorHomMap.precomp A K _ _ eK.inv ≫
      Stacks.HomComplex.TensorHomMap.postcomp A K _ L eL.hom ≫
        Stacks.HomComplex.TensorHomMap.precomp A K' K L f
  rw [← highUniverse_precomp_postcomp A f eL.hom]
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  rw [← Stacks.HomComplex.TensorHomMap.precomp_comp,
    ← Stacks.HomComplex.TensorHomMap.precomp_comp, hn]
  rfl

/-- For a K-injective complex `J`, derived Hom out of `L` is the Hom complex `Hom^•(L, J)`. -/
private noncomputable def highUniverseDerivedHomModelIso (A : Type u) [CommRing A]
    (L J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective] :
    (derivedHomAdjunctionOverRing.{u, v} A).hom.obj
        (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR A L J) := by
  let e := uliftModuleEquivalence.{u, max v u, v} A
  let ec := e.mapHomologicalComplex (.up ℤ)
  let L' := ec.inverse.obj L
  let J' := ec.inverse.obj J
  haveI : CochainComplex.IsKInjective J' := liftedComplex_isKInjective A J
  let eL := derivedCounitIso A L
  let eJ := derivedCounitIso A J
  let step1 := (derivedHomAdjunctionOverRing.{u, v} A).hom.mapIso
    (eL.op.prod eJ.symm)
  let step2 := derivedHomModelIso.{u, v} A L' J'
  let step3 := scalarDerivedFactorsApp A
    (CochainComplex.HomComplexR (ULift.{v} A) L' J')
  haveI : IsIso (scalarHomComplexMap A L' J') := scalarHomComplexMap_isIso A L' J'
  let step4 := DerivedCategory.Q.mapIso (asIso (scalarHomComplexMap A L' J'))
  let step5 := DerivedCategory.Q.mapIso (homComplexCounitIso A L J)
  exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step4 ≪≫ step5

/-- The derived counit of the restriction-of-scalars equivalence is natural in the complex. -/
private theorem derivedCounitIso_naturality (A : Type u) [CommRing A]
    {L L' : CochainComplex (ModuleCat.{max v u} A) ℤ} (f : L' ⟶ L) :
    (derivedScalarEquivalence.{u, v} A).functor.map
        (DerivedCategory.Q.map
          (((uliftModuleEquivalence.{u, max v u, v} A).mapHomologicalComplex
            (.up ℤ)).inverse.map f)) ≫
      (derivedCounitIso A L).hom =
    (derivedCounitIso A L').hom ≫ DerivedCategory.Q.map f := by
  let e := uliftModuleEquivalence.{u, max v u, v} A
  let ec := e.mapHomologicalComplex (.up ℤ)
  have hc : (e.functor.mapHomologicalComplex (.up ℤ)).map (ec.inverse.map f) ≫
      (complexCounitIso A L).hom =
      (complexCounitIso A L').hom ≫ f := by
    simpa [ec, complexCounitIso] using
      (ec.counitIso.hom.naturality f)
  dsimp only [derivedCounitIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, scalarDerivedFactorsApp_naturality A (ec.inverse.map f),
    Category.assoc, ← DerivedCategory.Q.map_comp, hc, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rfl

/-- The K-injective Hom model over `ULift A` is compatible with precomposition. -/
private theorem derivedHomModelIso_precomp (A : Type u) [CommRing A]
    {L L' : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ}
    (J : CochainComplex (ModuleCat.{max v u} (ULift.{v} A)) ℤ) [J.IsKInjective]
    (f : L' ⟶ L) :
    (derivedHomAdjunctionOverRing.{u, v} A).hom.map
        (show (Opposite.op ((derivedScalarEquivalence.{u, v} A).functor.obj
                  (DerivedCategory.Q.obj L)),
                (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj J)) ⟶
              (Opposite.op ((derivedScalarEquivalence.{u, v} A).functor.obj
                  (DerivedCategory.Q.obj L')),
                (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj J)) from
          (((derivedScalarEquivalence.{u, v} A).functor.map (DerivedCategory.Q.map f)).op,
            𝟙 _)) ≫
      (derivedHomModelIso.{u, v} A L' J).hom =
    (derivedHomModelIso.{u, v} A L J).hom ≫
      (derivedScalarEquivalence.{u, v} A).functor.map
        (DerivedCategory.Q.map
          (Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} A) L' L J f)) := by
  dsimp only [derivedHomModelIso, Iso.trans_hom]
  have hfac := (derivedHomULiftIso.{u, v} A).hom.naturality
    (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ⟶
      (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj J) from
      ((DerivedCategory.Q.map f).op, 𝟙 _))
  have hfac' :
      (derivedHomAdjunctionOverRing.{u, v} A).hom.map
          (show (Opposite.op ((derivedScalarEquivalence.{u, v} A).functor.obj
                    (DerivedCategory.Q.obj L)),
                  (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj J)) ⟶
                (Opposite.op ((derivedScalarEquivalence.{u, v} A).functor.obj
                    (DerivedCategory.Q.obj L')),
                  (derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj J)) from
            (((derivedScalarEquivalence.{u, v} A).functor.map (DerivedCategory.Q.map f)).op,
              𝟙 _)) ≫
        (derivedHomULiftIso.{u, v} A).hom.app
          (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj J) =
        (derivedHomULiftIso.{u, v} A).hom.app
          (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ≫
        (derivedScalarEquivalence.{u, v} A).functor.map
          ((derivedHomAdjunctionULift.{u, v} (R := A)).hom.map
            (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ⟶
              (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj J) from
              ((DerivedCategory.Q.map f).op, 𝟙 _))) := by
    simpa [Functor.comp_map, Functor.prod_map, Functor.op_map] using hfac
  simp only [Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hfac']
  have hn := (derivedHomAdjunctionULift.{u, v} (R := A)).homIso_naturality
    f (𝟙 J)
  simp only [DerivedCategory.Q.map_id, Stacks.HomComplex.TensorHomMap.postcomp_id,
    Category.comp_id] at hn
  rw [Category.assoc, ← Functor.map_comp, hn, Functor.map_comp]
  simp only [Category.assoc]

/-- A functor on `Cᵒᵖ × D` intertwines a naturality square in the first variable, written with
isomorphisms `a, a'`, with the corresponding square for `mapIso`. -/
private theorem map_op_prod_mapIso_naturality
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (G : Cᵒᵖ × D ⥤ E) {X X' Y Y' : C} {Z W : D} (a : X ≅ Y) (a' : X' ≅ Y') (b : Z ≅ W)
    (f : Y' ⟶ Y) (g : X' ⟶ X) (h : a'.hom ≫ f = g ≫ a.hom) :
    G.map (show (Opposite.op Y, W) ⟶ (Opposite.op Y', W) from (f.op, 𝟙 W)) ≫
        (G.mapIso (a'.op.prod b.symm)).hom =
      (G.mapIso (a.op.prod b.symm)).hom ≫
        G.map (show (Opposite.op X, Z) ⟶ (Opposite.op X', Z) from (g.op, 𝟙 Z)) := by
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  apply Prod.ext
  · exact congrArg Quiver.Hom.op h
  · simp

/-- The K-injective Hom model is compatible with precomposition. -/
private theorem highUniverseDerivedHomModelIso_precomp
    (A : Type u) [CommRing A]
    {L L' : CochainComplex (ModuleCat.{max v u} A) ℤ}
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (f : L' ⟶ L) :
    (derivedHomAdjunctionOverRing.{u, v} A).hom.map
        (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ⟶
          (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj J) from
          ((DerivedCategory.Q.map f).op, 𝟙 _)) ≫
      (highUniverseDerivedHomModelIso A L' J).hom =
    (highUniverseDerivedHomModelIso A L J).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp A L' L J f) := by
  let e := uliftModuleEquivalence.{u, max v u, v} A
  let ec := e.mapHomologicalComplex (.up ℤ)
  let F := (derivedScalarEquivalence.{u, v} A).functor
  let D := (derivedHomAdjunctionOverRing.{u, v} A).hom
  let L₀ := ec.inverse.obj L
  let L₀' := ec.inverse.obj L'
  let J₀ := ec.inverse.obj J
  let f₀ := ec.inverse.map f
  let cL := derivedCounitIso A L
  let cL' := derivedCounitIso A L'
  let cJ := derivedCounitIso A J
  have h₁ := map_op_prod_mapIso_naturality D cL cL' cJ (DerivedCategory.Q.map f)
    (F.map (DerivedCategory.Q.map f₀)) (derivedCounitIso_naturality A f).symm
  have : CochainComplex.IsKInjective J₀ := liftedComplex_isKInjective A J
  let ψ₀ := Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} A) L₀' L₀ J₀ f₀
  let ψ := Stacks.HomComplex.TensorHomMap.precomp A L' L J f
  have h₂ := derivedHomModelIso_precomp A J₀ f₀
  have h₃ := scalarDerivedFactorsApp_naturality A ψ₀
  have h₄ := scalarHomComplexMap_precomp A (L := J₀) f₀
  have h₅ := homComplexCounitIso_precomp A (L := J) f
  have h₄Q := congrArg (fun g ↦ DerivedCategory.Q.map g) h₄
  have h₅Q := congrArg (fun g ↦ DerivedCategory.Q.map g) h₅
  simp only [Functor.map_comp] at h₄Q h₅Q
  dsimp only [D, F, L₀, L₀', J₀, f₀, ec, e] at h₁ h₂ h₃ h₄Q h₅Q
  simp only [Functor.mapIso_hom] at h₁
  dsimp only [highUniverseDerivedHomModelIso, Iso.trans_hom]
  simp only [Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄Q, h₅Q]

/-- Derived Hom from `A/𝔪^(n+1)` into `K` is the Hom complex `Hom^•(A/𝔪^(n+1)[0], J)` for a
K-injective complex `J` representing `K`. -/
private noncomputable def derivedHom_maximalIdealPower_modelIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) (n : ℕ) :
    (derivedHomFiniteLengthFunctor.{u, v} A K).obj
        (Opposite.op (⟨maximalIdealPowerQuotientModule A n,
          maximalIdealPowerQuotientModule_isFiniteLength A n⟩ :
            FiniteLengthModules.{u, v} A)) ≅
      DerivedCategory.Q.obj
        ((highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J).obj n) := by
  let M := maximalIdealPowerQuotientModule A n
  let eM := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).app M
  let d := derivedHomAdjunctionOverRing.{u, v} A
  change d.hom.obj (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj M), K) ≅
    DerivedCategory.Q.obj (CochainComplex.HomComplexR A
      (highUniverseQuotientSingle A (IsLocalRing.maximalIdeal A ^ (n + 1))) J)
  exact d.hom.mapIso (eM.symm.op.prod eJ.symm) ≪≫
    highUniverseDerivedHomModelIso A _ J

/-- The Hom model is compatible with the transition maps of the system of quotients. -/
private theorem derivedHom_maximalIdealPower_modelIso_naturality
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) (n : ℕ) :
    (quotientPowerFiniteLengthFunctor A ⋙
        derivedHomFiniteLengthFunctor.{u, v} A K).map
          (homOfLE (Nat.le_succ n)) ≫
      (derivedHom_maximalIdealPower_modelIso A K J eJ (n + 1)).hom =
    (derivedHom_maximalIdealPower_modelIso A K J eJ n).hom ≫
      ((highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J) ⋙
        DerivedCategory.Q).map (homOfLE (Nat.le_succ n)) := by
  let M := maximalIdealPowerQuotientModule A n
  let M' := maximalIdealPowerQuotientModule A (n + 1)
  let t : M' ⟶ M := highUniverseQuotientPowerSucc A (IsLocalRing.maximalIdeal A) (n + 1)
  let S := CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0
  let s := S.map t
  let U := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0
  let eM := U.app M
  let eM' := U.app M'
  let d := derivedHomAdjunctionOverRing.{u, v} A
  have h₁ := map_op_prod_mapIso_naturality d.hom eM.symm eM'.symm eJ
    ((DerivedCategory.singleFunctor _ 0).map t) (DerivedCategory.Q.map s)
    (U.inv.naturality t).symm
  have h₂ := highUniverseDerivedHomModelIso_precomp A J s
  simp only [Functor.comp_map, quotientPowerFiniteLengthFunctor,
    highUniverseHomPowersComplex, Functor.ofSequence_map_homOfLE_succ]
  show d.hom.map
      (show (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj M), K) ⟶
        (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj M'), K) from
        (((DerivedCategory.singleFunctor _ 0).map t).op, 𝟙 _)) ≫
    ((d.hom.mapIso (eM'.symm.op.prod eJ.symm)).hom ≫
      (highUniverseDerivedHomModelIso A (S.obj M') J).hom) =
    ((d.hom.mapIso (eM.symm.op.prod eJ.symm)).hom ≫
      (highUniverseDerivedHomModelIso A (S.obj M) J).hom) ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp A (S.obj M') (S.obj M) J s)
  rw [← Category.assoc, h₁, Category.assoc, h₂]
  simp only [Category.assoc]

/-- The Hom complex out of `A/𝔪^(n+1)[0]` into a K-injective representative of a normalized
dualizing complex has no cohomology outside degree zero. -/
private theorem highUniverseHomPowers_homology_isZero_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) (n : ℕ) (q : ℤ) (hq : q ≠ 0) :
    IsZero (((highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J).obj n).homology
      q) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q
  let X := (highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J).obj n
  let e : H.obj ((derivedHomFiniteLengthFunctor.{u, v} A K).obj
        (Opposite.op (⟨maximalIdealPowerQuotientModule A n,
          maximalIdealPowerQuotientModule_isFiniteLength A n⟩ :
            FiniteLengthModules.{u, v} A))) ≅ X.homology q :=
    H.mapIso (derivedHom_maximalIdealPower_modelIso A K J eJ n) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} A) q).app X
  exact (derivedHom_maximalIdealPower_homology_isZero_of_ne_zero A K hK E i hi n q hq).of_iso
    e.symm


/-- Local cohomology of a normalized dualizing complex at the closed point has no cohomology
outside degree zero. -/
private theorem highUniverseHomPowers_colimit_homology_isZero_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).obj
      ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
        (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).ι.obj
        ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
          (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).obj K))) := by
  let F := highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max v u} A) (.up ℤ) q
  have hc : IsZero (colimit F) := by
    rw [IsZero.iff_id_eq_zero]
    refine colimit.hom_ext fun n ↦ ?_
    rw [Category.comp_id, comp_zero]
    exact (highUniverseHomPowers_homology_isZero_of_ne_zero
      A K hK E i hi J eJ n q hq).eq_of_src _ _
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).mapIso
      (localCohomology_modelIso A (IsLocalRing.maximalIdeal A) K J eJ) ≪≫
    highUniverseLocalCohomology_homologyIsoColimit A (IsLocalRing.maximalIdeal A) J q
  exact hc.of_iso e

/-- The system of derived Homs out of the quotients `A/𝔪^(n+1)` is the system of Hom complexes
into a K-injective representative. -/
private noncomputable def derivedHomPowerDiagramIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) :
    quotientPowerFiniteLengthFunctor A ⋙
        derivedHomFiniteLengthFunctor.{u, v} A K ≅
      highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J ⋙
        DerivedCategory.Q := by
  let F := quotientPowerFiniteLengthFunctor A ⋙
    derivedHomFiniteLengthFunctor.{u, v} A K
  let G := highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J ⋙
    DerivedCategory.Q
  let t : F ⟶ G := NatTrans.ofSequence
    (fun n ↦ (derivedHom_maximalIdealPower_modelIso A K J eJ n).hom)
    (fun n ↦ derivedHom_maximalIdealPower_modelIso_naturality A K J eJ n)
  exact NatIso.ofComponents (fun n ↦ derivedHom_maximalIdealPower_modelIso A K J eJ n)
    (fun f ↦ t.naturality f)

/-- Matlis duality on the system of quotients `A/𝔪^(n+1)` is the system `n ↦ Hom_A(A/𝔪^(n+1), E)`
placed in degree zero. -/
private noncomputable def matlisPowerDiagramIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A) :
    quotientPowerFiniteLengthFunctor A ⋙
        matlisDualFiniteLengthFunctor.{u, v} A E ≅
      matlisPowerModuleFunctor A E ⋙
        DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0 := by
  let F := quotientPowerFiniteLengthFunctor A ⋙
    matlisDualFiniteLengthFunctor.{u, v} A E
  let G := matlisPowerModuleFunctor A E ⋙
    DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  let c (n : ℕ) : F.obj n ≅ G.obj n := by
    change (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (maximalIdealPowerQuotientModule A n ⟶ E)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (maximalIdealPowerQuotientModule A n ⟶ E))
    exact Iso.refl _
  let t : F ⟶ G := NatTrans.ofSequence
    (fun n ↦ (c n).hom)
    (fun n ↦ by
      change F.map (homOfLE (Nat.le_succ n)) =
        G.map (homOfLE (Nat.le_succ n))
      dsimp only [F, G]
      simp only [Functor.comp_map]
      congr 1
      ext f
      simp only [quotientPowerFiniteLengthFunctor, matlisPowerModuleFunctor,
        Functor.ofSequence_map_homOfLE_succ]
      change ((MonoidalClosed.pre (C := ModuleCat.{max v u} A)
        (highUniverseQuotientPowerSucc A
        (IsLocalRing.maximalIdeal A) (n + 1))).app E).hom f =
        (highUniverseQuotientPowerSucc A (IsLocalRing.maximalIdeal A) (n + 1)) ≫ f
      rfl)
  exact NatIso.ofComponents c (fun f ↦ t.naturality f)

/-- Degree-zero local cohomology of a normalized dualizing complex at the closed point is an
injective hull of the residue field. -/
private theorem nonempty_localCohomologyHomologyZeroIsoInjectiveHull
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (J : CochainComplex (ModuleCat.{max v u} A) ℤ) [J.IsKInjective]
    (eJ : DerivedCategory.Q.obj J ≅ K) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
      ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
        (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).ι.obj
        ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
          (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))).obj K)) ≅ E) := by
  obtain ⟨e⟩ := derivedHomFiniteLengthIsoMatlisDual.{u, v} A K hK E i hi
  let P := quotientPowerFiniteLengthFunctor A
  let M := matlisPowerModuleFunctor A E
  let X := highUniverseHomPowersComplex A (IsLocalRing.maximalIdeal A) J
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0
  let Hc := HomologicalComplex.homologyFunctor (ModuleCat.{max v u} A) (.up ℤ) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  let eD : X ⋙ Hc ≅ M :=
    (Functor.associator X DerivedCategory.Q H ≪≫
      Functor.isoWhiskerLeft X
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} A) 0)).symm ≪≫
    Functor.isoWhiskerRight (derivedHomPowerDiagramIso A K J eJ).symm H ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft P e) H ≪≫
    Functor.isoWhiskerRight (matlisPowerDiagramIso A E) H ≪≫
    Functor.associator M S H ≪≫
    Functor.isoWhiskerLeft M
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) 0) ≪≫
    Functor.rightUnitor M
  exact ⟨H.mapIso (localCohomology_modelIso A (IsLocalRing.maximalIdeal A) K J eJ) ≪≫
    highUniverseLocalCohomology_homologyIsoColimit A
      (IsLocalRing.maximalIdeal A) J 0 ≪≫
    HasColimit.isoOfNatIso eD ≪≫
    matlisPowerModuleColimitIso A E i hi⟩

/-- An essential monomorphism stays essential after composing with an isomorphism. -/
private lemma isEssentialMono_comp_iso
    {C : Type w} [Category C] [HasZeroObject C] [HasPullbacks C]
    {M E E' : C} (i : M ⟶ E) [Mono i] (e : E ≅ E')
    (hi : Module.IsEssentialMono i) :
    Module.IsEssentialMono (i ≫ e.hom) := by
  let o := (Subobject.mapIso e).toOrderIso
  have hmk : o (Subobject.mk i) = Subobject.mk (i ≫ e.hom) := rfl
  intro Q hQ
  have hQ' : o.symm Q ≠ ⊥ := fun h ↦ hQ (by simpa using congrArg o h)
  have h := hi (o.symm Q) hQ'
  have hm : o (o.symm Q ⊓ Subobject.mk i) ≠ ⊥ := by
    intro hbot
    apply h
    apply o.injective
    simpa using hbot
  rwa [o.map_inf, o.apply_symm_apply, hmk] at hm

/-- Every object of the derived category is represented by a K-injective complex. -/
private theorem exists_kInjectiveRepresentative (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) :
    ∃ J : CochainComplex (ModuleCat.{max v u} A) ℤ,
      J.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj J ≅ K) := by
  let : EnoughInjectives (ModuleCat.{max v u} A) := ModuleCat.enoughInjectives A
  obtain ⟨J, f, hf, hJ⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage K)
  refine ⟨J, hJ, ⟨?_⟩⟩
  have : QuasiIso f := hf
  exact (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K

/-- The degree-zero local cohomology of a normalized dualizing complex at the closed point is an
injective hull of the residue field. -/
@[stacks 0A82 "injective hull"]
public theorem exists_isInjectiveHull_homology_zero_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    let m := IsLocalRing.maximalIdeal A
    let hm : m.FG := IsNoetherian.noetherian m
    let L := (derivedPowerTorsionProperty A m hm).ι.obj
      ((localCohomologyFunctor A m hm).obj K)
    let E := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj L
    ∃ (i : (ModuleCat.uliftFunctor.{v} A).obj
          (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
        (hi : Mono i),
      @Module.IsInjectiveHull (ModuleCat.{max v u} A) _ _ _ _ _ i hi := by
  obtain ⟨E', i, hi, hull⟩ := exists_residueFieldInjectiveHull.{u, v} A
  let : Mono i := hi
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_kInjectiveRepresentative.{u, v} A K
  let : J.IsKInjective := hJ
  obtain ⟨e⟩ := nonempty_localCohomologyHomologyZeroIsoInjectiveHull A K hK E' i hull J eJ
  exact ⟨i ≫ e.inv, inferInstance, Injective.of_iso e.symm hull.1,
    isEssentialMono_comp_iso i e.symm hull.2⟩

/-- Local cohomology of a normalized dualizing complex at the closed point is its degree-zero
cohomology module placed in degree zero. -/
@[stacks 0A82 "concentration in degree zero"]
public theorem nonempty_localCohomology_iso_single_homology_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    let m := IsLocalRing.maximalIdeal A
    let hm : m.FG := IsNoetherian.noetherian m
    let L := (derivedPowerTorsionProperty A m hm).ι.obj
      ((localCohomologyFunctor A m hm).obj K)
    let E := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj L
    Nonempty (L ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj E) := by
  obtain ⟨E, i, hi, hull⟩ := exists_residueFieldInjectiveHull.{u, v} A
  let : Mono i := hi
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_kInjectiveRepresentative.{u, v} A K
  let : J.IsKInjective := hJ
  exact DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero _ 0 fun q hq ↦
    highUniverseHomPowers_colimit_homology_isZero_of_ne_zero A K hK E i hull J eJ q hq

end Dualizing.LocalDuality

end
