module

public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedCotangentBaseMapIntrinsic
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleProdFirstVertexNaturality
public import StacksFrontier.Deformation.ToposThickening.SolutionBaseRestriction

/-!
# Naturality of the obstruction class of Tag 08V5 in the problem

Let `S` and `T` be square-zero extension problems of ringed topoi (Tag 08UF) over the same
morphism `f : X ⟶ B`, and let a morphism `S ⟶ T` be given: a map `φ : O_{B'_S} ⟶ O_{B'_T}` of
thickened bases over `O_B`, a compatible map of ideals `ι : f⁻¹J_S ⟶ f⁻¹J_T`, and a map
`k : G_S ⟶ G_T` of target modules with `c_T ∘ ι = k ∘ c_S`. This file proves that the obstruction
classes `o = −(δ.comp γ)` of `RingedToposExtensionProblem.canonicalObstructionClass` correspond:
`o(S) ≫ k[2] = o(T)` in `Ext²_O(L_{O/f⁻¹O_B}, G_T)`. This is the naturality of obstruction
classes in the deformation situation that condition (ii) of [Stacks, Tag 07YX] asks for, at the
level of extension problems.

Only the first ring of the tower `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O` changes. The connecting morphism `δ` of
the fundamental triangle is natural in it
(`CategoryTheory.Sheaf.towerConnecting_naturality_baseChange`), and the map of first vertices is
the intrinsic one (`CategoryTheory.Sheaf.baseChangedCotangentBaseMapIntrinsic`). What remains is
the class `γ`. Through `H^{-1}(L_{A/A'}) = I/I²`, the change-of-base map of cotangent complexes is
the map of conormal sheaves. This file proves that by comparing both with the conormal sheaf of
the degree-zero term of the standard resolution, into which `I/I²` injects.

## Main definitions

All names are in the namespace `Deformation.ToposThickening`.

* `CotangentObstruction.conormalBaseMap`: the map `I₁/I₁² ⟶ I₂/I₂²` induced by `k : A₁ ⟶ A₂`
  over `B`.

## Main results

* `CotangentObstruction.homologyMap_towerCotangentChangeOfBase_conormalIso_hom`:
  on `H^{-1}`, the change-of-base map `L_{B/A₁} ⟶ L_{B/A₂}` is `I₁/I₁² ⟶ I₂/I₂²`.
* `CotangentObstruction.baseExtEquiv_Q_map_changeOfBase_comp`:
  `baseExtEquiv` is natural in the base ring.
* `CotangentObstruction.Q_map_baseChangedCotangentBaseMap_comp_towerBaseClass`:
  `γ` is natural in the base ring.
* `CotangentObstruction.towerConnecting_comp_towerBaseClass_naturality`:
  `δ ≫ γ[1]` is natural in the base ring and the target.
* `RingedToposExtensionProblem.canonicalObstructionClass_comp_map`:
  `o(S) ≫ k[2] = o(T)`.

## References

* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite Simplicial

universe t u v' u' w'

namespace Deformation.ToposThickening.CotangentObstruction

open CategoryTheory.Sheaf Stacks.Sites.Conormal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective CommRingCat.{u}]
  {A₁ A₂ B : Sheaf J CommRingCat.{u}} (k : A₁ ⟶ A₂) (g : A₂ ⟶ B)

/-- **The map of conormal sheaves `I₁/I₁² ⟶ I₂/I₂²` induced by `k`**, for the quotients
`k ≫ g : A₁ ⟶ B` and `g : A₂ ⟶ B`. -/
abbrev conormalBaseMap [Presheaf.IsLocallySurjective J g.hom]
    [Presheaf.IsLocallySurjective J (k ≫ g).hom] :
    conormalSheaf.{u, u, u, u} J A₁ B (k ≫ g) ⟶ conormalSheaf.{u, u, u, u} J A₂ B g :=
  conormalSheafMapOfSquare.{u, u, u, u} J A₁ A₂ B B (k ≫ g) g k (𝟙 B)
    (Category.comp_id _).symm

/-- The map `I/I² ⟶ C_{P₀/B}` of conormal sheaves along the base map `A ⟶ P₀` of the standard
resolution of a locally surjective `g : A ⟶ B` is a monomorphism. -/
theorem mono_conormalSheafMapOfFac_resolutionBase [Presheaf.IsLocallySurjective J g.hom] :
    Mono (conormalSheafMapOfFac.{u, u, u, u} J B A₂ (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) g
      (resolutionAugmentation J g (op ⦋0⦌)) (resolutionBase.{u, u, u} J g (op ⦋0⦌))
      (resolutionBase_comp_resolutionAugmentation g)) := by
  have gen :=
    Stacks.SheafOfModules.naiveCotangentHomologyNegOneIsoConormal_hom_conormalSheafMapOfFac.{u,
    u, u, u} J A₂ B g _ (resolutionBase.{u, u, u} J g (op ⦋0⦌))
    (resolutionAugmentation J g (op ⦋0⦌)) (resolutionBase_comp_resolutionAugmentation g)
    (resolutionZeroIsoFreeAlgebra J g)
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J g)
    (resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom J g)
  have h2 := (Iso.eq_inv_comp _).2 gen
  refine @mono_of_mono _ _ _ _ _ _ (conormalSheafIsoOfFac.{u, u, u, u} J B _ _ _ _ _
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J g)).hom ?_
  rw [h2]
  refine @mono_comp _ _ _ _ _ _ ?_ _ (@mono_comp _ _ _ _ _ _ ?_ _ ?_)
  · infer_instance
  · exact HomologicalComplex.mono_homologyToX _ _ _
  · exact @IsIso.mono_of_iso _ _ _ _ _ (CategoryTheory.instIsIsoEqToHom _)

variable [Presheaf.IsLocallySurjective J g.hom] [Presheaf.IsLocallySurjective J (k ≫ g).hom]

/-- **The change-of-base map `L_{B/A₁} ⟶ L_{B/A₂}` on `H^{-1}` is the map of conormal sheaves**
`I₁/I₁² ⟶ I₂/I₂²` induced by `k`, through `H^{-1}(L_{B/A}) = I/I²`. -/
theorem homologyMap_towerCotangentChangeOfBase_conormalIso_hom :
    HomologicalComplex.homologyMap (towerCotangentChangeOfBase.{u, u, u} J k g) (-1) ≫
        (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).hom =
      (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J (k ≫ g)).hom ≫
        conormalBaseMap k g := by
  have := mono_conormalSheafMapOfFac_resolutionBase g
  refine (cancel_mono (conormalSheafMapOfFac.{u, u, u, u} J B A₂
    (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) g (resolutionAugmentation J g (op ⦋0⦌))
    (resolutionBase.{u, u, u} J g (op ⦋0⦌)) (resolutionBase_comp_resolutionAugmentation g))).1 ?_
  refine (cancel_epi ((cotangentComplex.{u, u, u} J (k ≫ g)).homologyπ (-1))).1 ?_
  let sq := towerFunctorialitySquare.{u, u, u} J k g
  have hH₁ := homologyπ_conormalIso_hom_conormalSheafMapOfFac (k ≫ g)
  have hH₂ := homologyπ_conormalIso_hom_conormalSheafMapOfFac g
  have hu : (towerCotangentChangeOfBase.{u, u, u} J k g).f (-1) =
      (cotangentComplex_degreeIso.{u, u, u} J (k ≫ g) 1).hom ≫
        squareCotangentTermMap sq (op ⦋1⦌) ≫
          (squareRestrict.{u, u, u} J (𝟙 B)).map
            (cotangentComplex_degreeIso.{u, u, u} J g 1).inv :=
    squareCotangentComplexMap_f _ 1
  have hs := squareCotangentTermMap_comp_naiveComparisonNegOne sq
  have hid : ∀ {M N : targetModules.{u, u, u} J B} (φ : M ⟶ N),
      (squareRestrict.{u, u, u} J (𝟙 B)).map φ = φ := fun _ => rfl
  have hcong : ∀ (ψ ψ' : A₁ ⟶ resolutionTerm.{u, u, u} J g (op ⦋0⦌)) (_ : ψ = ψ')
      (h : ψ ≫ resolutionAugmentation J g (op ⦋0⦌) = (k ≫ g) ≫ 𝟙 B)
      (h' : ψ' ≫ resolutionAugmentation J g (op ⦋0⦌) = (k ≫ g) ≫ 𝟙 B),
      conormalSheafMapOfSquare.{u, u, u, u} J A₁ _ B B (k ≫ g) _ ψ (𝟙 B) h =
        conormalSheafMapOfSquare.{u, u, u, u} J A₁ _ B B (k ≫ g) _ ψ' (𝟙 B) h' := by
    rintro _ _ rfl _ _
    rfl
  have hR₁ := conormalSheafMapOfSquare_comp_map_conormalSheafMapOfFac (J := J) (A₁ := A₁)
    (A₂ := A₂) (A₃ := resolutionTerm.{u, u, u} J g (op ⦋0⦌)) (B₁ := B) (B₂ := B) (φ₁ := k ≫ g)
    (φ₂ := g) (φ₃ := resolutionAugmentation J g (op ⦋0⦌)) (ψ := k) (β := 𝟙 B)
    (χ := resolutionBase.{u, u, u} J g (op ⦋0⦌)) (Category.comp_id _).symm
    (resolutionBase_comp_resolutionAugmentation g)
  have hR₂ := conormalSheafMapOfFac_comp_conormalSheafMapOfSquare (J := J) (A₀ := A₁)
    (A₁ := resolutionTerm.{u, u, u} J (k ≫ g) (op ⦋0⦌))
    (A₂ := resolutionTerm.{u, u, u} J g (op ⦋0⦌)) (B₁ := B) (B₂ := B) (φ₀ := k ≫ g)
    (φ₁ := resolutionAugmentation J (k ≫ g) (op ⦋0⦌))
    (φ₂ := resolutionAugmentation J g (op ⦋0⦌))
    (χ₀ := resolutionBase.{u, u, u} J (k ≫ g) (op ⦋0⦌)) (ψ := sq.resolution (op ⦋0⦌))
    (β := 𝟙 B) (resolutionBase_comp_resolutionAugmentation (k ≫ g))
    (sq.resolution_augmentation (op ⦋0⦌))
  rw [hid] at hR₁
  rw [hcong _ _ (sq.resolution_base (op ⦋0⦌)) _ ((Category.assoc _ _ _).trans
    (congrArg (k ≫ ·) (resolutionBase_comp_resolutionAugmentation g)))] at hR₂
  have hci : HomologicalComplex.cyclesMap (towerCotangentChangeOfBase.{u, u, u} J k g) (-1) ≫
      (cotangentComplex.{u, u, u} J g).iCycles (-1) =
    (cotangentComplex.{u, u, u} J (k ≫ g)).iCycles (-1) ≫
      (towerCotangentChangeOfBase.{u, u, u} J k g).f (-1) :=
    HomologicalComplex.cyclesMap_i _ _
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyπ_naturality_assoc, hH₂]
  have key : squareCotangentTermMap sq (op ⦋1⦌) ≫
      (squareRestrict.{u, u, u} J (𝟙 B)).map (cotangentComplex_degreeIso.{u, u, u} J g 1).inv ≫
        (cotangentComplex_degreeIso.{u, u, u} J g 1).hom ≫ naiveComparisonNegOne J g =
      naiveComparisonNegOne J (k ≫ g) ≫
        conormalSheafMapOfSquare.{u, u, u, u} J (resolutionTerm.{u, u, u} J (k ≫ g) (op ⦋0⦌))
          (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) B B (resolutionAugmentation J (k ≫ g) (op ⦋0⦌))
          (resolutionAugmentation J g (op ⦋0⦌)) (sq.resolution (op ⦋0⦌)) (𝟙 B)
          (sq.resolution_augmentation (op ⦋0⦌)) := by
    have e : (squareRestrict.{u, u, u} J (𝟙 B)).map
          (cotangentComplex_degreeIso.{u, u, u} J g 1).inv ≫
        (cotangentComplex_degreeIso.{u, u, u} J g 1).hom ≫ naiveComparisonNegOne J g =
        (squareRestrict.{u, u, u} J (𝟙 B)).map (naiveComparisonNegOne J g) := by
      show (squareRestrict.{u, u, u} J (𝟙 B)).map
          (cotangentComplex_degreeIso.{u, u, u} J g 1).inv ≫ (squareRestrict.{u, u, u} J (𝟙 B)).map
          ((cotangentComplex_degreeIso.{u, u, u} J g 1).hom ≫ naiveComparisonNegOne J g) = _
      rw [← Functor.map_comp, Iso.inv_hom_id_assoc]
    rw [e]
    exact hs
  have hL : (towerCotangentChangeOfBase.{u, u, u} J k g).f (-1) ≫
      (cotangentComplex_degreeIso.{u, u, u} J g 1).hom ≫ naiveComparisonNegOne J g =
      (cotangentComplex_degreeIso.{u, u, u} J (k ≫ g) 1).hom ≫ naiveComparisonNegOne J (k ≫ g) ≫
        conormalSheafMapOfSquare.{u, u, u, u} J (resolutionTerm.{u, u, u} J (k ≫ g) (op ⦋0⦌))
          (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) B B (resolutionAugmentation J (k ≫ g) (op ⦋0⦌))
          (resolutionAugmentation J g (op ⦋0⦌)) (sq.resolution (op ⦋0⦌)) (𝟙 B)
          (sq.resolution_augmentation (op ⦋0⦌)) := by
    rw [hu]
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans key))
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hci).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hL)))).trans
    (((reassoc_of% hH₁) _).symm.trans
      (congrArg (fun t => (cotangentComplex.{u, u, u} J (k ≫ g)).homologyπ (-1) ≫
        (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J (k ≫ g)).hom ≫ t)
        (hR₂.trans hR₁.symm)))

variable {O : Sheaf J CommRingCat.{u}} (h : B ⟶ O)
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)] (G : targetModules.{u, u, u} J O)

omit [J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)] in
/-- Extension of scalars commutes with the change-of-base map on `H^{-1}`, through
`H^{-1}(L ⊗_B O) = H^{-1}(L) ⊗_B O`. -/
theorem extendScalarsCotangentHomologyNegOneIso_inv_comp_homologyMap :
    (extendScalarsCotangentHomologyNegOneIso.{u, u, u} J (k ≫ g) h).inv ≫
    HomologicalComplex.homologyMap (((towerExtendScalars.{u, u, u} J h).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (towerCotangentChangeOfBase.{u, u, u} J k g)) (-1) =
    (towerExtendScalars.{u, u, u} J h).map
        (HomologicalComplex.homologyMap (towerCotangentChangeOfBase.{u, u, u} J k g) (-1)) ≫
      (extendScalarsCotangentHomologyNegOneIso.{u, u, u} J g h).inv := by
  have hE := ShortComplex.homologyMap_map_comp_homologyMapIsoOfLeftHomologyData_hom
    (towerExtendScalars.{u, u, u} J h) (cotangentNegOneData.{u, u, u} J (k ≫ g))
    (cotangentNegOneData.{u, u, u} J g)
    ((HomologicalComplex.shortComplexFunctor _ _ (-1)).map
      (towerCotangentChangeOfBase.{u, u, u} J k g))
  exact (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 hE).trans (Category.assoc _ _ _))

/-- **`baseExtEquiv` is natural in the base ring.** A map `L_{B/A₂} ⊗_B O ⟶ G[1]`, precomposed
with the change of base along `k` extended to `O`, corresponds to the map `I₂/I₂² ⟶ G` attached to
it precomposed with `I₁/I₁² ⟶ I₂/I₂²`. -/
theorem baseExtEquiv_Q_map_changeOfBase_comp
    (x : DerivedCategory.Q.obj (baseChangedComplex.{u, u, u} J g h) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) :
    baseExtEquiv.{u, u, u} J (k ≫ g) h G
        (DerivedCategory.Q.map (((towerExtendScalars.{u, u, u} J h).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (towerCotangentChangeOfBase.{u, u, u} J k g)) ≫ x) =
      conormalBaseMap k g ≫ baseExtEquiv.{u, u, u} J g h G x := by
  have hB := homologyMap_towerCotangentChangeOfBase_conormalIso_hom k g
  have hB' : (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J (k ≫ g)).inv ≫
      HomologicalComplex.homologyMap (towerCotangentChangeOfBase.{u, u, u} J k g) (-1) =
      conormalBaseMap k g ≫ (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hB, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hE' := extendScalarsCotangentHomologyNegOneIso_inv_comp_homologyMap k g h
  show (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J (k ≫ g)).inv ≫
      (towerExtendRestrictAdjunction.{u, u, u} J h).homEquiv _ _
        ((extendScalarsCotangentHomologyNegOneIso.{u, u, u} J (k ≫ g) h).inv ≫
          DerivedCategory.negOneHomologyMap _ G
            (DerivedCategory.Q.map (((towerExtendScalars.{u, u, u} J h).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (towerCotangentChangeOfBase.{u, u, u} J k g)) ≫ x) ≫
            𝟙 _) ≫ 𝟙 _ =
    conormalBaseMap k g ≫ (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv ≫
      (towerExtendRestrictAdjunction.{u, u, u} J h).homEquiv _ _
        ((extendScalarsCotangentHomologyNegOneIso.{u, u, u} J g h).inv ≫
          DerivedCategory.negOneHomologyMap _ G x ≫ 𝟙 _) ≫ 𝟙 _
  rw [DerivedCategory.negOneHomologyMap_Q_map_comp]
  have step : (extendScalarsCotangentHomologyNegOneIso.{u, u, u} J (k ≫ g) h).inv ≫
      (HomologicalComplex.homologyMap (((towerExtendScalars.{u, u, u} J h).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (towerCotangentChangeOfBase.{u, u, u} J k g)) (-1) ≫
          DerivedCategory.negOneHomologyMap _ G x) ≫ 𝟙 G =
      (towerExtendScalars.{u, u, u} J h).map
          (HomologicalComplex.homologyMap (towerCotangentChangeOfBase.{u, u, u} J k g) (-1)) ≫
        (extendScalarsCotangentHomologyNegOneIso.{u, u, u} J g h).inv ≫
          DerivedCategory.negOneHomologyMap _ G x ≫ 𝟙 G :=
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hE').trans (Category.assoc _ _ _)))
  refine (congrArg (fun t => (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J (k ≫ g)).inv ≫
    (towerExtendRestrictAdjunction.{u, u, u} J h).homEquiv _ _ t ≫ 𝟙 _) step).trans ?_
  rw [Adjunction.homEquiv_naturality_left]
  have aux : ∀ {P Q R S T : targetModules.{u, u, u} J B} (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ S)
      (d : S ⟶ R) (W : R ⟶ T), a ≫ b = c ≫ d → a ≫ (b ≫ W) ≫ 𝟙 T = c ≫ d ≫ W ≫ 𝟙 T := by
    intro _ _ _ _ _ a b c d W e
    rw [Category.comp_id, Category.comp_id, ← Category.assoc, e, Category.assoc]
  exact aux _ _ _ _ _ hB'

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The class `γ` of a conormal map is natural in the base ring**: along the map of first
vertices `L_{B/A₁} ⊗_B O ⟶ L_{B/A₂} ⊗_B O` of the fundamental triangles, the class of
`c : I₂/I₂² ⟶ G` pulls back to the class of `c` precomposed with `I₁/I₁² ⟶ I₂/I₂²`. -/
theorem Q_map_baseChangedCotangentBaseMap_comp_towerBaseClass
    (c : conormalSheaf.{u, u, u, u} J A₂ B g ⟶ (squareRestrict.{u, u, u} J h).obj G) :
    DerivedCategory.Q.map (baseChangedCotangentBaseMap.{u, u, u} J k g h) ≫
        towerBaseClass G g h c =
      towerBaseClass G (k ≫ g) h (conormalBaseMap k g ≫ c) := by
  rw [baseChangedCotangentBaseMapIntrinsic, towerBaseClass, towerBaseClass]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc DerivedCategory.Q (towerExtendScalarsCotangentComplexIso.{u, u, u} J
    g h).hom, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  congr 1
  rw [Equiv.eq_symm_apply, baseExtEquiv_Q_map_changeOfBase_comp, Equiv.apply_symm_apply]

omit [Presheaf.IsLocallySurjective J (k ≫ g).hom] in
/-- **The composite `δ ≫ γ[1]` of the fundamental triangle is natural in the base ring and in the
target.** Let `g₁ = k ≫ g`. For `c₁ : I₁/I₁² ⟶ G₁` and `c₂ : I₂/I₂² ⟶ G₂` compatible with
`I₁/I₁² ⟶ I₂/I₂²` and `k_G : G₁ ⟶ G₂`, the classes `δ ≫ γ(c)[1]` of the towers
`A₁ ⟶ B ⟶ O` and `A₂ ⟶ B ⟶ O` in `Ext²_O(L_{O/B}, −)` correspond under `k_G`. -/
theorem towerConnecting_comp_towerBaseClass_naturality {g₁ : A₁ ⟶ B} (hg : k ≫ g = g₁)
    [Presheaf.IsLocallySurjective J g₁.hom] {G₁ G₂ : targetModules.{u, u, u} J O} (kG : G₁ ⟶ G₂)
    (c₁ : conormalSheaf.{u, u, u, u} J A₁ B g₁ ⟶ (squareRestrict.{u, u, u} J h).obj G₁)
    (c₂ : conormalSheaf.{u, u, u, u} J A₂ B g ⟶ (squareRestrict.{u, u, u} J h).obj G₂)
    (hc : c₁ ≫ (squareRestrict.{u, u, u} J h).map kG =
      conormalSheafMapOfSquare.{u, u, u, u} J A₁ A₂ B B g₁ g k (𝟙 B)
        (by rw [Category.comp_id, hg]) ≫ c₂) :
    (towerConnecting.{t, u, u, u} J g₁ h ≫ (towerBaseClass G₁ g₁ h c₁)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app _) ≫
        ((DerivedCategory.singleFunctor _ 0).map kG)⟦(2 : ℤ)⟧' =
      towerConnecting.{t, u, u, u} J g h ≫ (towerBaseClass G₂ g h c₂)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app _ := by
  subst hg
  have hγ : towerBaseClass G₁ (k ≫ g) h c₁ ≫
      ((DerivedCategory.singleFunctor _ 0).map kG)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (baseChangedCotangentBaseMap.{u, u, u} J k g h) ≫
        towerBaseClass G₂ g h c₂ := by
    rw [← towerBaseClass_comp, hc, Q_map_baseChangedCotangentBaseMap_comp_towerBaseClass]
    rfl
  have hμ := ((shiftFunctorAdd' (DerivedCategory (targetModules.{u, u, u} J O)) (1 : ℤ) 1 2
    (by norm_num)).inv.naturality ((DerivedCategory.singleFunctor _ 0).map kG))
  simp only [Functor.comp_map] at hμ
  rw [Category.assoc, Category.assoc, ← hμ,
    ← Category.assoc ((towerBaseClass G₁ (k ≫ g) h c₁)⟦(1 : ℤ)⟧'),
    ← Functor.map_comp, hγ, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    towerConnecting_naturality_baseChange, Category.assoc]

end Deformation.ToposThickening.CotangentObstruction

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.Conormal

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

/-- **Naturality of the obstruction class of Tag 08V5 in the problem.** Let `S` and `T` be
square-zero extension problems over the same morphism `f₀ : X ⟶ B` (`hS : S.f = f₀`,
`hT : T.f = f₀`), and let a morphism `S ⟶ T` be given:

* `φ : O_{B'_S} ⟶ O_{B'_T}` over `O_B`;
* a map of ideals `ι : f⁻¹J_S ⟶ f⁻¹J_T` compatible with `f⁻¹φ`;
* `k : G_S ⟶ G_T` with `c_T ∘ ι = k ∘ c_S`.

Then `o(S) ∈ Ext²_O(L_{O/f⁻¹O_B}, G_S)` is carried by `k` to `o(T)`: `o(S) ≫ k[2] = o(T)`, both
read on `L_{O/f₀⁻¹O_B}`. The morphism is named separately from `S.f` and `T.f` so that, when both
are `f₀` by definition, the identifications are `𝟙` without comparing `S` and `T`. -/
theorem canonicalObstructionClass_comp_map {S T : RingedToposExtensionProblem X B}
    {f₀ : RingedToposHom X B} (hS : S.f = f₀) (hT : T.f = f₀)
    (φ : S.baseExtension ⟶ T.baseExtension) (hφ : φ ≫ T.baseReduction = S.baseReduction)
    (k : S.G ⟶ T.G) (ι : ∀ U : X.Cᵒᵖ, S.I.val.obj U → T.I.val.obj U)
    (hι : ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
      ((inverseImageCommRingFunctor f₀.toToposHom).map φ).hom.app U
          (cast (congrArg (fun f : RingedToposHom X B =>
              (((inverseImageCommRingFunctor f.toToposHom).obj S.baseExtension).obj.obj U :
                Type u)) hS)
            (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
              S.idealInclusion.val.app U a)) =
        cast (congrArg (fun f : RingedToposHom X B =>
            (((inverseImageCommRingFunctor f.toToposHom).obj T.baseExtension).obj.obj U :
                Type u)) hT)
          (show ((inverseImageCommRingFunctor T.f.toToposHom).obj T.baseExtension).obj.obj U from
            T.idealInclusion.val.app U (ι U a)))
    (hk : ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
      (show T.G.val.obj U from T.c.val.app U (ι U a)) =
        k.val.app U (show S.G.val.obj U from S.c.val.app U a)) :
    eqToHom (congrArg (fun f : RingedToposHom X B =>
        Sheaf.cotangentComplexDerived.{u, u, u, t} X.J f.fSharpInverseImage) hS.symm) ≫
      (show Sheaf.cotangentComplexDerived.{u, u, u, t} X.J S.f.fSharpInverseImage ⟶
        ((DerivedCategory.singleFunctor _ 0).obj (targetG.{u, u, u} S))⟦(2 : ℤ)⟧ from
          S.canonicalObstructionClass) ≫
        ((DerivedCategory.singleFunctor _ 0).map k)⟦(2 : ℤ)⟧' =
      eqToHom (congrArg (fun f : RingedToposHom X B =>
          Sheaf.cotangentComplexDerived.{u, u, u, t} X.J f.fSharpInverseImage) hT.symm) ≫
        (show Sheaf.cotangentComplexDerived.{u, u, u, t} X.J T.f.fSharpInverseImage ⟶
          ((DerivedCategory.singleFunctor _ 0).obj (targetG.{u, u, u} T))⟦(2 : ℤ)⟧ from
            T.canonicalObstructionClass) := by
  subst hS
  obtain ⟨fT, baseT, redT, lsT, sqT, IT, GT, inclT, cT, zT, uT⟩ := T
  obtain rfl : fT = S.f := hT
  rw [eqToHom_refl, Category.id_comp, Category.id_comp]
  let T : RingedToposExtensionProblem X B :=
    ⟨S.f, baseT, redT, lsT, sqT, IT, GT, inclT, cT, zT, uT⟩
  have := isLocallySurjective_baseReductionInverseImage T
  let K := (inverseImageCommRingFunctor S.f.toToposHom).map φ
  have hg : K ≫ T.baseReductionInverseImage = S.baseReductionInverseImage :=
    (Functor.map_comp _ _ _).symm.trans (congrArg _ hφ)
  have hc : S.baseConormalMap ≫ (Sheaf.squareRestrict.{u, u, u} X.J S.f.fSharpInverseImage).map k =
      conormalSheafMapOfSquare.{u, u, u, u} X.J _ _ _ _ S.baseReductionInverseImage
        T.baseReductionInverseImage K (𝟙 _) (by rw [Category.comp_id, hg]) ≫
        T.baseConormalMap := by
    rw [← baseConormalMap_mapTarget]
    refine conormal_hom_ext S.baseReductionInverseImage _ fun U x => ?_
    refine ((S.mapTarget k).baseConormalMap_conormalClass U x).trans ?_
    refine Eq.trans ?_ (congrArg (T.baseConormalMap.val.app U)
      (conormalSheafMapOfSquare_conormalClass.{u, u, u, u} X.J S.thickenedBaseInverseImage
        T.thickenedBaseInverseImage _ _ _ _ (𝟙 _) (𝟙 _) S.baseReductionInverseImage
        T.baseReductionInverseImage K (𝟙 _) (by rw [Category.comp_id, hg]) U x)).symm
    refine Eq.trans ?_ (T.baseConormalMap_conormalClass U _).symm
    refine congrArg ((singleShiftAutomorphism T).hom.val.app U) ?_
    refine Eq.trans ?_ (congrArg (fun a => (show T.G.val.obj U from T.c.val.app U a))
      (T.kernelPreimage_eq _ (ι U (S.kernelPreimage x))
        ((hι U _).symm.trans (congrArg _ (S.idealInclusion_kernelPreimage x))))).symm
    exact (hk U _).symm
  have hM := CotangentObstruction.towerConnecting_comp_towerBaseClass_naturality K
    T.baseReductionInverseImage S.f.fSharpInverseImage hg k S.baseConormalMap T.baseConormalMap hc
  exact (Preadditive.neg_comp _ _).trans (congrArg Neg.neg hM)

end Deformation.ToposThickening.RingedToposExtensionProblem

end
