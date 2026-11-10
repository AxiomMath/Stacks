module

public import Mathlib.Algebra.Homology.Functor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Cotangent.PerfectVanishing
public import StacksFrontier.Cotangent.ProductDecompositionBase
public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestriction
public import StacksFrontier.Cotangent.SheavesOfRings.ProductRings
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonSquareNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# The cotangent complex of a product of two sheaves of rings is the direct sum

Let `C` be a site and let `f : A ⟶ B`, `f' : A ⟶ B'` be homomorphisms of sheaves of commutative
rings on `C`. This file proves that the canonical map

`L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}`

of `CategoryTheory.Sheaf.prodCotangentComparison`, the pairing of the maps of cotangent complexes
induced by the two projections, is an isomorphism in `D(B ⨯ B')`, together with the corresponding
statements on the sections over every object `U` and on the presheaf models
`U ↦ L_{B(U)/A(U)}` of the cotangent complexes.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseSquareMap`: the map of presheaf models
  `U ↦ L_{B(U)/A(U)}` ⟶ `U ↦ L_{B'(U)/A'(U)}` induced by a commutative square of homomorphisms of
  sheaves of commutative rings.
* `CategoryTheory.Sheaf.sectionwiseProdComparison`: the comparison map of Tag 08SY on the
  presheaf models.

## Main results

* `CommAlgCat.quasiIso_biprodLift_cotangentComplexAbMap`: for `A`-algebras `D`, `B`, `C` and maps
  identifying `D` with `B × C`, the pair `L_{D/A} ⟶ L_{B/A} ⊕ L_{C/A}` of the induced maps of
  cotangent complexes is a quasi-isomorphism.
* `CategoryTheory.Sheaf.bijective_prod_sections`: the projections identify `(B ⨯ B')(U)` with
  `B(U) × B'(U)`.
* `CategoryTheory.Sheaf.quasiIso_sectionsProdComparison`: the comparison map of Tag 08SY on
  sections over `U` is a quasi-isomorphism.
* `CategoryTheory.Sheaf.quasiIso_sectionwiseProdComparison`: the comparison map on the presheaf
  models is a quasi-isomorphism.
* `CategoryTheory.Sheaf.quasiIso_prodCotangentComparison`: the comparison map
  `L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}` is a quasi-isomorphism of complexes of sheaves of
  `B ⨯ B'`-modules.
* `CategoryTheory.Sheaf.isIso_prodCotangentComparisonDerived`: the comparison map is an
  isomorphism in `D(B ⨯ B')`.

## References

* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SY](https://stacks.math.columbia.edu/tag/08SY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CommAlgCat

universe u

variable {A : Type u} [CommRing A]

/-- Let `D`, `B`, `C` be `A`-algebras and let `sq₁ : D → B`, `sq₂ : D → C` be squares over the
identity of `A` whose maps of algebras jointly identify `D` with `B × C`. Then the pair of the two
induced maps of cotangent complexes, `L_{D/A} ⟶ L_{B/A} ⊕ L_{C/A}`, is a quasi-isomorphism of
complexes of abelian groups. -/
theorem quasiIso_biprodLift_cotangentComplexAbMap {D B C : CommAlgCat.{u} A}
    (sq₁ : AlgebraSquare.{u, u, u} A A D B) (sq₂ : AlgebraSquare.{u, u, u} A A D C)
    (h₁ : sq₁.base = RingHom.id A) (h₂ : sq₂.base = RingHom.id A)
    (hbij : Function.Bijective fun x : D => (sq₁.map x, sq₂.map x)) :
    QuasiIso (biprod.lift (cotangentComplexAbMap.{u, u, u} sq₁)
      (cotangentComplexAbMap.{u, u, u} sq₂)) := by
  obtain ⟨b₁, m₁, hm₁⟩ := sq₁
  obtain ⟨b₂, m₂, hm₂⟩ := sq₂
  subst h₁ h₂
  let E : AlgebraSquare.{u, u, u} A A D (CommAlgCat.of A (Prod (B : Type u) (C : Type u))) :=
    { base := RingHom.id A
      map := m₁.prod m₂
      map_algebraMap a := Prod.ext (hm₁ a) (hm₂ a) }
  have hE₁ : (⟨RingHom.id A, m₁, hm₁⟩ : AlgebraSquare.{u, u, u} A A D B) =
      E.comp (productFstSquare.{u, u} A B C) := rfl
  have hE₂ : (⟨RingHom.id A, m₂, hm₂⟩ : AlgebraSquare.{u, u, u} A A D C) =
      E.comp (productSndSquare.{u, u} A B C) := rfl
  have hiso : IsIso (cotangentComplexAbMap.{u, u, u} E) :=
    isIso_cotangentComplexAbMap_of_bijective E Function.bijective_id hbij
  let F := (forget₂ (ModuleCat.{u} (Prod (B : Type u) (C : Type u)))
    AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)
  have : F.Additive := inferInstance
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have : QuasiIso (cotangentComplexProductMap.{u, u} A B C) :=
    quasiIso_cotangentComplexProductMap A B C
  let X := ((ModuleCat.restrictScalars (productFstSquare.{u, u} A B C).map).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)
  let Y := ((ModuleCat.restrictScalars (productSndSquare.{u, u} A B C).map).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A C)
  have hq' : QuasiIso (biprod.lift (cotangentComplexAbMap.{u, u, u} (productFstSquare.{u, u} A B C))
      (cotangentComplexAbMap.{u, u, u} (productSndSquare.{u, u} A B C)) :
        F.obj (cotangentComplex.{u, u} A (CommAlgCat.of A (Prod (B : Type u) (C : Type u)))) ⟶
          F.obj X ⊞ F.obj Y) := by
    have hlift : (biprod.lift (cotangentComplexAbMap.{u, u, u} (productFstSquare.{u, u} A B C))
        (cotangentComplexAbMap.{u, u, u} (productSndSquare.{u, u} A B C)) :
          F.obj (cotangentComplex.{u, u} A (CommAlgCat.of A (Prod (B : Type u) (C : Type u)))) ⟶
            F.obj X ⊞ F.obj Y) =
        F.map (cotangentComplexProductMap.{u, u} A B C) ≫ (F.mapBiprod X Y).hom := by
      rw [cotangentComplexProductMap, biprod.map_lift_mapBiprod]
      rfl
    rw [hlift]
    infer_instance
  have hsplit : biprod.lift (cotangentComplexAbMap.{u, u, u}
        (⟨RingHom.id A, m₁, hm₁⟩ : AlgebraSquare.{u, u, u} A A D B))
        (cotangentComplexAbMap.{u, u, u}
          (⟨RingHom.id A, m₂, hm₂⟩ : AlgebraSquare.{u, u, u} A A D C)) =
      cotangentComplexAbMap.{u, u, u} E ≫
        biprod.lift (cotangentComplexAbMap.{u, u, u} (productFstSquare.{u, u} A B C))
          (cotangentComplexAbMap.{u, u, u} (productSndSquare.{u, u} A B C)) := by
    rw [hE₁, hE₂, cotangentComplexAbMap_comp, cotangentComplexAbMap_comp]
    apply biprod.hom_ext <;> simp
  rw [hsplit]
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := hq')

end CommAlgCat

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B B' : Sheaf J CommRingCat.{max u v w}}

/-- **Sections of a binary product of sheaves of commutative rings are the product of the
sections**: over every object `U` the two projections identify `(B ⨯ B')(U)` with
`B(U) × B'(U)`. -/
theorem bijective_prod_sections (U : Cᵒᵖ) :
    Function.Bijective fun x : (B ⨯ B').obj.obj U =>
      (((prod.fst : B ⨯ B' ⟶ B).hom.app U) x, ((prod.snd : B ⨯ B' ⟶ B').hom.app U) x) := by
  let G : Sheaf J CommRingCat.{max u v w} ⥤ Type (max u v w) :=
    sheafToPresheaf J CommRingCat.{max u v w} ⋙ (evaluation Cᵒᵖ CommRingCat.{max u v w}).obj U ⋙
      forget CommRingCat.{max u v w}
  let e := PreservesLimitPair.iso G B B' ≪≫ Types.binaryProductIso (G.obj B) (G.obj B')
  have h₁ : ∀ x, (e.hom x).1 = G.map (prod.fst : B ⨯ B' ⟶ B) x := fun x => by
    change ((Types.binaryProductIso _ _).hom ((PreservesLimitPair.iso G B B').hom x)).1 = _
    rw [Types.binaryProductIso_hom_comp_fst_apply, PreservesLimitPair.iso_hom]
    exact ConcreteCategory.congr_hom (prodComparison_fst G B B') x
  have h₂ : ∀ x, (e.hom x).2 = G.map (prod.snd : B ⨯ B' ⟶ B') x := fun x => by
    change ((Types.binaryProductIso _ _).hom ((PreservesLimitPair.iso G B B').hom x)).2 = _
    rw [Types.binaryProductIso_hom_comp_snd_apply, PreservesLimitPair.iso_hom]
    exact ConcreteCategory.congr_hom (prodComparison_snd G B B') x
  have he : (fun x : (B ⨯ B').obj.obj U =>
      (((prod.fst : B ⨯ B' ⟶ B).hom.app U) x, ((prod.snd : B ⨯ B' ⟶ B').hom.app U) x)) =
        e.hom :=
    funext fun x => Prod.ext (h₁ x).symm (h₂ x).symm
  rw [he]
  exact (isIso_iff_bijective e.hom).mp inferInstance

variable (f : A ⟶ B) (f' : A ⟶ B')

/-- **The comparison map of Tag 08SY on sections over `U` is a quasi-isomorphism.** The pair of
the maps of cotangent complexes of rings induced by the two projections of `B ⨯ B'`, taken on
sections over `U`, is a quasi-isomorphism
`L_{(B ⨯ B')(U)/A(U)} ⟶ L_{B(U)/A(U)} ⊕ L_{B'(U)/A(U)}` of complexes of abelian groups. -/
theorem quasiIso_sectionsProdComparison (U : Cᵒᵖ) :
    QuasiIso (biprod.lift
      (CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsSquare J (𝟙 A) _ (prodRingHom_square_fst J f f') U))
      (CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsSquare J (𝟙 A) _ (prodRingHom_square_snd J f f') U))) :=
  CommAlgCat.quasiIso_biprodLift_cotangentComplexAbMap _ _ rfl rfl
    (bijective_prod_sections J U)

end CategoryTheory.Sheaf

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  [Preadditive D] [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E]
  (F : D ⥤ E) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]

omit [HasBinaryBiproducts E] in
/-- A functor preserving binary biproducts carries `biprod.map u v` to `biprod.map` of the images,
up to the comparison isomorphisms. -/
lemma map_biprod_map_comp_mapBiprod_hom {X X' Y Y' : D} (u : X ⟶ X') (v : Y ⟶ Y') :
    F.map (biprod.map u v) ≫ (F.mapBiprod X' Y').hom =
      (F.mapBiprod X Y).hom ≫ biprod.map (F.map u) (F.map v) := by
  rw [Functor.mapBiprod_hom, Functor.mapBiprod_hom]
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, ← F.map_comp, biprod.map_fst, F.map_comp,
      Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
  · rw [Category.assoc, biprod.lift_snd, ← F.map_comp, biprod.map_snd, F.map_comp,
      Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

universe u v w t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ## The map of presheaf models induced by a square -/

section Square

variable {A A' B B' : Sheaf J CommRingCat.{max u v w}} {f : A ⟶ B} {f' : A' ⟶ B'}
  (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')

/-- The square on sections is natural in `U`: restricting and then applying the square on
sections over `V` is applying the square on sections over `U` and then restricting. -/
theorem sectionsRestrictionSquare_comp_sectionsSquare {U V : Cᵒᵖ} (g : U ⟶ V) :
    (sectionsRestrictionSquare J f g).comp (sectionsSquare J a b hsq V) =
      (sectionsSquare J a b hsq U).comp (sectionsRestrictionSquare J f' g) := by
  have hbase := congrArg CommRingCat.Hom.hom (a.hom.naturality g)
  have hmap := congrArg CommRingCat.Hom.hom (b.hom.naturality g)
  simp only [CommAlgCat.AlgebraSquare.comp, sectionsRestrictionSquare, sectionsSquare]
  congr 1

/-- **The map of presheaf models induced by a square.** A commutative square `a : A ⟶ A'`,
`b : B ⟶ B'` of homomorphisms of sheaves of commutative rings induces, over every `U`, the map
`L_{B(U)/A(U)} ⟶ L_{B'(U)/A'(U)}` of cotangent complexes of rings of the square on sections;
these form a map of complexes of presheaves of abelian groups. -/
noncomputable def sectionwiseSquareMap :
    sectionwiseCotangentPresheafComplex J f ⟶ sectionwiseCotangentPresheafComplex J f' where
  f j :=
    { app U := (CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsSquare J a b hsq U)).f j
      naturality _ _ g := congrArg (fun k => HomologicalComplex.Hom.f k j)
        ((CommAlgCat.cotangentComplexAbMap_comp _ _).symm.trans
          ((congrArg CommAlgCat.cotangentComplexAbMap
            (sectionsRestrictionSquare_comp_sectionsSquare J a b hsq g)).trans
            (CommAlgCat.cotangentComplexAbMap_comp _ _))) }
  comm' i j _ := NatTrans.ext (funext fun U =>
    (CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
      (sectionsSquare J a b hsq U)).comm i j)

/-- **The comparison maps of Tag 08SX intertwine the map of presheaf models induced by a square
with the map of cotangent complexes of sheaves induced by it.** -/
theorem sectionwiseSquareMap_comp_comparison :
    sectionwiseSquareMap J a b hsq ≫ sectionwiseCotangentPresheafComplexComparison J f' =
      sectionwiseCotangentPresheafComplexComparison J f ≫
        ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq))) := by
  ext j U x
  exact (sectionsCotangentComplexComparison_square J a b hsq U j x).symm

end Square

/-! ## The comparison map of Tag 08SY -/

variable {A B B' : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) (f' : A ⟶ B')

/-- The map of presheaf models induced by the first projection square,
`U ↦ L_{(B ⨯ B')(U)/A(U)}` ⟶ `U ↦ L_{B(U)/A(U)}`. -/
noncomputable def sectionwiseProdFst :
    sectionwiseCotangentPresheafComplex J (prodRingHom J f f') ⟶
      sectionwiseCotangentPresheafComplex J f :=
  sectionwiseSquareMap J (𝟙 A) _ (prodRingHom_square_fst J f f')

/-- The map of presheaf models induced by the second projection square,
`U ↦ L_{(B ⨯ B')(U)/A(U)}` ⟶ `U ↦ L_{B'(U)/A(U)}`. -/
noncomputable def sectionwiseProdSnd :
    sectionwiseCotangentPresheafComplex J (prodRingHom J f f') ⟶
      sectionwiseCotangentPresheafComplex J f' :=
  sectionwiseSquareMap J (𝟙 A) _ (prodRingHom_square_snd J f f')

/-- **The comparison map of Tag 08SY on the presheaf models**: the pair of the maps of presheaf
models induced by the two projection squares,
`U ↦ L_{(B ⨯ B')(U)/A(U)}` ⟶ `(U ↦ L_{B(U)/A(U)}) ⊕ (U ↦ L_{B'(U)/A(U)})`. -/
noncomputable def sectionwiseProdComparison :
    sectionwiseCotangentPresheafComplex J (prodRingHom J f f') ⟶
      sectionwiseCotangentPresheafComplex J f ⊞ sectionwiseCotangentPresheafComplex J f' :=
  biprod.lift (sectionwiseProdFst J f f') (sectionwiseProdSnd J f f')

/-- The first map of presheaf models is intertwined by the comparison maps of Tag 08SX with the
first component of the comparison map of Tag 08SY. -/
theorem sectionwiseProdFst_comp_comparison :
    sectionwiseProdFst J f f' ≫ sectionwiseCotangentPresheafComplexComparison J f =
      sectionwiseCotangentPresheafComplexComparison J (prodRingHom J f f') ≫
        ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
              (B ⨯ B'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (prodCotangentComponentFst J f f')) :=
  sectionwiseSquareMap_comp_comparison J (𝟙 A) _ (prodRingHom_square_fst J f f')

/-- The second map of presheaf models is intertwined by the comparison maps of Tag 08SX with the
second component of the comparison map of Tag 08SY. -/
theorem sectionwiseProdSnd_comp_comparison :
    sectionwiseProdSnd J f f' ≫ sectionwiseCotangentPresheafComplexComparison J f' =
      sectionwiseCotangentPresheafComplexComparison J (prodRingHom J f f') ≫
        ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
              (B ⨯ B'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (prodCotangentComponentSnd J f f')) :=
  sectionwiseSquareMap_comp_comparison J (𝟙 A) _ (prodRingHom_square_snd J f f')

/-- Evaluation at `U` of complexes of presheaves of abelian groups. -/
noncomputable abbrev evalComplex (U : Cᵒᵖ) :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  ((evaluation Cᵒᵖ AddCommGrpCat.{max u v w}).obj U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The presheaf model `U ↦ L_{B(U)/A(U)}`, evaluated at `U`, is `L_{B(U)/A(U)}`. -/
noncomputable def evalSectionwiseCotangentIso {D E : Sheaf J CommRingCat.{max u v w}}
    (g : D ⟶ E) (U : Cᵒᵖ) :
    (evalComplex.{u, v, w} (C := C) U).obj (sectionwiseCotangentPresheafComplex J g) ≅
      sectionsCotangentComplexAb J g U :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- Evaluated at `U`, the map of presheaf models induced by a square is the map of cotangent
complexes of rings induced by the square on sections. -/
theorem evalComplex_map_sectionwiseSquareMap {A A' B B' : Sheaf J CommRingCat.{max u v w}}
    {g : A ⟶ B} {g' : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B') (hsq : g ≫ b = a ≫ g') (U : Cᵒᵖ) :
    (evalComplex.{u, v, w} (C := C) U).map (sectionwiseSquareMap J a b hsq) ≫
        (evalSectionwiseCotangentIso J g' U).hom =
      (evalSectionwiseCotangentIso J g U).hom ≫
        CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) := by
  ext j x
  rfl

/-- Evaluated at `U`, the comparison map of Tag 08SY on the presheaf models is, up to the
identifications of `evalSectionwiseCotangentIso`, the comparison map on sections. -/
theorem evalComplex_map_sectionwiseProdComparison (U : Cᵒᵖ)
    [PreservesBinaryBiproducts (evalComplex.{u, v, w} (C := C) U)] :
    (evalSectionwiseCotangentIso J (prodRingHom J f f') U).hom ≫ biprod.lift
        (CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J (𝟙 A) _ (prodRingHom_square_fst J f f') U))
        (CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J (𝟙 A) _ (prodRingHom_square_snd J f f') U)) =
      ((evalComplex.{u, v, w} (C := C) U).map (sectionwiseProdComparison J f f') ≫
        ((evalComplex.{u, v, w} (C := C) U).mapBiprod (sectionwiseCotangentPresheafComplex J f)
          (sectionwiseCotangentPresheafComplex J f')).hom) ≫
        (biprod.mapIso (evalSectionwiseCotangentIso J f U)
          (evalSectionwiseCotangentIso J f' U)).hom := by
  rw [sectionwiseProdComparison, biprod.map_lift_mapBiprod, biprod.mapIso_hom,
    biprod.lift_map, biprod.comp_lift, sectionwiseProdFst, sectionwiseProdSnd,
    ← evalComplex_map_sectionwiseSquareMap, ← evalComplex_map_sectionwiseSquareMap]

/-- Evaluated at `U`, the comparison map of Tag 08SY on the presheaf models is a
quasi-isomorphism. -/
theorem quasiIso_evalComplex_map_sectionwiseProdComparison (U : Cᵒᵖ) :
    QuasiIso ((evalComplex.{u, v, w} (C := C) U).map (sectionwiseProdComparison J f f')) := by
  have : PreservesBinaryBiproducts (evalComplex.{u, v, w} (C := C) U) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have h₀ := quasiIso_comp (evalSectionwiseCotangentIso J (prodRingHom J f f') U).hom _
    (hφ := quasiIso_of_isIso _) (hφ' := quasiIso_sectionsProdComparison J f f' U)
  rw [evalComplex_map_sectionwiseProdComparison] at h₀
  exact (quasiIso_iff_comp_right _ _).mp ((quasiIso_iff_comp_right _ _).mp h₀)

/-- **The comparison map of Tag 08SY on the presheaf models is a quasi-isomorphism.** -/
theorem quasiIso_sectionwiseProdComparison : QuasiIso (sectionwiseProdComparison J f f') :=
  (HomologicalComplex.quasiIso_iff_evaluation _).2
    (quasiIso_evalComplex_map_sectionwiseProdComparison J f f')

/-- The underlying complex of sheaves of abelian groups of a complex of sheaves of
`B ⨯ B'`-modules. -/
noncomputable abbrev toSheafComplex :
    CochainComplex (targetModules.{u, v, w} J (B ⨯ B')) ℤ ⥤
      CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ :=
  (SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (B ⨯ B'))).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- The underlying presheaves of a complex of sheaves of abelian groups. -/
noncomputable abbrev toPresheafComplex :
    CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ ⥤
      CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ :=
  (sheafToPresheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sheafification of complexes of presheaves of abelian groups. -/
noncomputable abbrev sheafifyComplex :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ ⥤
      CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ :=
  (presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The comparison map of Tag 08SY on underlying complexes of sheaves of abelian groups, with its
target written as the direct sum of the two underlying complexes. -/
noncomputable abbrev prodCotangentComparisonAb :
    cotangentComplexAb J (prodRingHom J f f') ⟶
      cotangentComplexAb J f ⊞ cotangentComplexAb J f' :=
  biprod.lift ((toSheafComplex J (B := B) (B' := B')).map (prodCotangentComponentFst J f f'))
    ((toSheafComplex J (B := B) (B' := B')).map (prodCotangentComponentSnd J f f'))

/-- The pair of the comparison maps of Tag 08SX for `A ⟶ B` and `A ⟶ B'`, a map from the direct
sum of the two presheaf models to the underlying presheaves of the direct sum of the two
cotangent complexes. -/
noncomputable def sectionwiseProdTargetComparison
    [PreservesBinaryBiproducts (toPresheafComplex.{u, v, w} J)] :
    sectionwiseCotangentPresheafComplex J f ⊞ sectionwiseCotangentPresheafComplex J f' ⟶
      (toPresheafComplex.{u, v, w} J).obj (cotangentComplexAb J f ⊞ cotangentComplexAb J f') :=
  biprod.map (sectionwiseCotangentPresheafComplexComparison J f)
      (sectionwiseCotangentPresheafComplexComparison J f') ≫
    ((toPresheafComplex.{u, v, w} J).mapBiprod (cotangentComplexAb J f)
      (cotangentComplexAb J f')).inv

/-- The pair of the comparison maps of Tag 08SX is inverted by sheafification. -/
theorem isIso_sheafify_sectionwiseProdTargetComparison
    [PreservesBinaryBiproducts (toPresheafComplex.{u, v, w} J)]
    [PreservesBinaryBiproducts (sheafifyComplex.{u, v, w} J)] :
    IsIso ((sheafifyComplex.{u, v, w} J).map (sectionwiseProdTargetComparison J f f')) := by
  have := isIso_sheafify_sectionwiseCotangentPresheafComplexComparison J f
  have := isIso_sheafify_sectionwiseCotangentPresheafComplexComparison J f'
  have h := (sheafifyComplex.{u, v, w} J).map_biprod_map_comp_mapBiprod_hom
    (sectionwiseCotangentPresheafComplexComparison J f)
    (sectionwiseCotangentPresheafComplexComparison J f')
  rw [← Iso.eq_comp_inv] at h
  have : IsIso (biprod.map
      ((sheafifyComplex.{u, v, w} J).map (sectionwiseCotangentPresheafComplexComparison J f))
      ((sheafifyComplex.{u, v, w} J).map (sectionwiseCotangentPresheafComplexComparison J f'))) :=
    (biprod.mapIso
      (asIso ((sheafifyComplex.{u, v, w} J).map
        (sectionwiseCotangentPresheafComplexComparison J f)))
      (asIso ((sheafifyComplex.{u, v, w} J).map
        (sectionwiseCotangentPresheafComplexComparison J f')))).isIso_hom
  have : IsIso ((sheafifyComplex.{u, v, w} J).map
      (biprod.map (sectionwiseCotangentPresheafComplexComparison J f)
        (sectionwiseCotangentPresheafComplexComparison J f'))) := by
    rw [h]
    infer_instance
  rw [sectionwiseProdTargetComparison, Functor.map_comp]
  infer_instance

/-- The pair of the comparison maps of Tag 08SX is, in every degree, inverted by
sheafification. -/
theorem W_sectionwiseProdTargetComparison_f
    [PreservesBinaryBiproducts (toPresheafComplex.{u, v, w} J)]
    [PreservesBinaryBiproducts (sheafifyComplex.{u, v, w} J)] (n : ℤ) :
    J.W ((sectionwiseProdTargetComparison J f f').f n) := by
  have := isIso_sheafify_sectionwiseProdTargetComparison J f f'
  exact (J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J _) _).mpr
    (inferInstanceAs (IsIso (((sheafifyComplex.{u, v, w} J).map
      (sectionwiseProdTargetComparison J f f')).f n)))

/-- The comparison maps of Tag 08SX intertwine the comparison map of Tag 08SY on the presheaf
models with the comparison map of Tag 08SY on underlying complexes of sheaves of abelian
groups. -/
theorem sectionwiseProdComparison_comp_targetComparison
    [PreservesBinaryBiproducts (toPresheafComplex.{u, v, w} J)] :
    sectionwiseProdComparison J f f' ≫ sectionwiseProdTargetComparison J f f' =
      sectionwiseCotangentPresheafComplexComparison J (prodRingHom J f f') ≫
        (toPresheafComplex.{u, v, w} J).map (prodCotangentComparisonAb J f f') := by
  have hcomm' : sectionwiseProdComparison J f f' ≫
      biprod.map (sectionwiseCotangentPresheafComplexComparison J f)
        (sectionwiseCotangentPresheafComplexComparison J f') =
      sectionwiseCotangentPresheafComplexComparison J (prodRingHom J f f') ≫
        (toPresheafComplex.{u, v, w} J).map (prodCotangentComparisonAb J f f') ≫
          ((toPresheafComplex.{u, v, w} J).mapBiprod (cotangentComplexAb J f)
            (cotangentComplexAb J f')).hom := by
    rw [sectionwiseProdComparison, biprod.lift_map, sectionwiseProdFst_comp_comparison,
      sectionwiseProdSnd_comp_comparison, prodCotangentComparisonAb]
    erw [biprod.map_lift_mapBiprod]
    exact (biprod.comp_lift _ _ _).symm
  rw [sectionwiseProdTargetComparison, ← Category.assoc, hcomm', Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The comparison map of Tag 08SY is a quasi-isomorphism on underlying complexes of sheaves of
abelian groups. -/
theorem quasiIso_prodCotangentComparisonAb : QuasiIso (prodCotangentComparisonAb J f f') := by
  have : PreservesBinaryBiproducts (toPresheafComplex.{u, v, w} J) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts (sheafifyComplex.{u, v, w} J) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have := quasiIso_sectionwiseProdComparison J f f'
  exact quasiIso_of_sectionwise J (sectionwiseCotangentPresheafComplexComparison J _)
    (sectionwiseProdTargetComparison J f f')
    (W_sectionwiseCotangentPresheafComplexComparison_f J _)
    (W_sectionwiseProdTargetComparison_f J f f') (prodCotangentComparisonAb J f f')
    (sectionwiseProdComparison J f f') (sectionwiseProdComparison_comp_targetComparison J f f')

/-- The comparison map of Tag 08SY on underlying complexes of sheaves of abelian groups is the
image of the comparison map of complexes of sheaves of modules, followed by the identification of
the image of a direct sum with the direct sum of the images. -/
theorem toSheafComplex_map_prodCotangentComparison
    [PreservesBinaryBiproducts (toSheafComplex.{u, v, w} J (B := B) (B' := B'))] :
    (toSheafComplex.{u, v, w} J (B := B) (B' := B')).map (prodCotangentComparison J f f') ≫
      ((toSheafComplex.{u, v, w} J (B := B) (B' := B')).mapBiprod
        (prodCotangentSummandFst J f (B' := B')) (prodCotangentSummandSnd J f' (B := B))).hom =
      (prodCotangentComparisonAb J f f' :
        (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
            (cotangentComplex J (prodRingHom J f f')) ⟶
          (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
              (prodCotangentSummandFst J f (B' := B')) ⊞
            (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
              (prodCotangentSummandSnd J f' (B := B))) := by
  rw [prodCotangentComparison, biprod.map_lift_mapBiprod]
  rfl

/-- The comparison map of Tag 08SY is a quasi-isomorphism on underlying complexes of sheaves of
abelian groups, read on the image of the comparison map of complexes of sheaves of modules. -/
theorem quasiIso_toSheafComplex_map_prodCotangentComparison :
    QuasiIso ((toSheafComplex.{u, v, w} J (B := B) (B' := B')).map
      (prodCotangentComparison J f f')) := by
  have : (SheafOfModules.toSheaf.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (B ⨯ B'))).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesBinaryBiproducts (toSheafComplex.{u, v, w} J (B := B) (B' := B')) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have hAb : QuasiIso (prodCotangentComparisonAb J f f' :
      (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
          (cotangentComplex J (prodRingHom J f f')) ⟶
        (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
            (prodCotangentSummandFst J f (B' := B')) ⊞
          (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
            (prodCotangentSummandSnd J f' (B := B))) :=
    quasiIso_prodCotangentComparisonAb J f f'
  exact (quasiIso_iff_of_arrow_mk_iso
    ((toSheafComplex.{u, v, w} J (B := B) (B' := B')).map (prodCotangentComparison J f f'))
    (prodCotangentComparisonAb J f f' :
      (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
          (cotangentComplex J (prodRingHom J f f')) ⟶
        (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
            (prodCotangentSummandFst J f (B' := B')) ⊞
          (toSheafComplex.{u, v, w} J (B := B) (B' := B')).obj
            (prodCotangentSummandSnd J f' (B := B)))
    (Arrow.isoMk (Iso.refl _)
      ((toSheafComplex.{u, v, w} J (B := B) (B' := B')).mapBiprod
        (prodCotangentSummandFst J f (B' := B')) (prodCotangentSummandSnd J f' (B := B)))
      (by rw [Iso.refl_hom, Category.id_comp]
          exact (toSheafComplex_map_prodCotangentComparison J f f').symm))).mpr hAb

/-- **The comparison map of Tag 08SY is a quasi-isomorphism**: the canonical map
`L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}` of complexes of sheaves of `B ⨯ B'`-modules induces an
isomorphism on every cohomology sheaf. -/
theorem quasiIso_prodCotangentComparison : QuasiIso (prodCotangentComparison J f f') := by
  have hT := quasiIso_toSheafComplex_map_prodCotangentComparison J f f'
  let := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (B ⨯ B'))
  have : (SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (B ⨯ B'))).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (B ⨯ B')))).mp hT

/-- Let `C` be a site and let `A ⟶ B`, `A ⟶ B'` be homomorphisms of sheaves of commutative rings
on `C`. Then the canonical map `L_{B ⨯ B'/A} ⟶ L_{B/A} ⊕ L_{B'/A}`
(`CategoryTheory.Sheaf.prodCotangentComparisonDerived`, the pairing of the maps of cotangent
complexes induced by the two projections) is an isomorphism in `D(B ⨯ B')`. -/
@[stacks 08SY "the lemma: the canonical map L_{B×B'/A} → L_{B/A} ⊕ L_{B'/A}, the pairing of the \
  maps induced by the two projections, is an isomorphism in D(B×B'), for an arbitrary site and \
  arbitrary homomorphisms A → B, A → B' of sheaves of rings"]
theorem isIso_prodCotangentComparisonDerived
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J (B ⨯ B'))] :
    IsIso (prodCotangentComparisonDerived.{u, v, w, t} J f f') :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_prodCotangentComparison J f f')

end CategoryTheory.Sheaf

end
