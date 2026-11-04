module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDistinguished
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionRestrictionMap
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated
public import StacksFrontier.CategoryTheory.Triangulated.DistinguishedOfIso
public import StacksFrontier.CategoryTheory.Triangulated.TransposeLocus

/-!
# Derived sections over an object of a chaotic site are weakly exact

Let `C` be a category, viewed as a site with the chaotic topology, let `O` be a sheaf of rings on
it and let `(A, d)` be a sheaf of differential graded `O`-algebras. For an object `U` of `C` the
derived sections `RΓ(U, -) : D(A, d) ⥤ D(A(U), d)` are computed by taking sections over `U` of
any differential graded `A`-module. This file shows that `RΓ(U, -)` carries the first two
morphisms of a distinguished triangle of `D(A, d)` to the first two morphisms of a distinguished
triangle of `D(A(U), d)`, which is the part of the exactness of `RΓ(U, -)` that does not involve
the translation.

Taking sections over `U` is exact on a chaotic site and carries graded splittings of an
admissible short exact sequence of differential graded `A`-modules to graded splittings of the
sequence of section modules. Every distinguished triangle of `D(A, d)` is, up to isomorphism, the
image of the cone sequence `L ⟶ C(f) ⟶ K[1]` of a homomorphism `f : K ⟶ L` of differential graded
`A`-modules, and that sequence is admissible.

## Main results

* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.exists_iso_coneRotatedTriangle`:
  every distinguished triangle of `K(Mod(A, d))` is isomorphic to the triangle of the cone
  sequence of a homomorphism.
* `SheafOfModules.DifferentialGradedModule.derivedSections_isWeaklyTriangulated`: **derived
  sections over an object of a chaotic site are weakly triangulated.**

## References

* [Stacks Project, Lemma 24.33.2 (Tag 0GZA)](https://stacks.math.columbia.edu/tag/0GZA)
* [Stacks Project, Tag 09QU](https://stacks.math.columbia.edu/tag/09QU)
* [Stacks Project, Tag 09K8](https://stacks.math.columbia.edu/tag/09K8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

section GradedSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {M N P : DifferentialGradedModule.{t, a, a} A}

variable {K L : DifferentialGradedModule.{t, a, a} A} {f : K ⟶ L} {g : L ⟶ M}

end GradedSections

/-! ### Distinguished triangles of the homotopy category as cone sequences -/

section ConeTriangle

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

namespace HomotopyCategory

/-- **Every distinguished triangle of `K(Mod(A, d))` is isomorphic to the triangle of the cone
sequence `L ⟶ C(f) ⟶ K[1]` of a homomorphism `f : K ⟶ L`.** -/
theorem exists_iso_coneRotatedTriangle (T : Triangle (HomotopyCategory.{u, v, v} A))
    (hT : T ∈ distTriang (HomotopyCategory.{u, v, v} A)) :
    ∃ (K L : DifferentialGradedModule.{u, v, v} A) (f : K ⟶ L),
      Nonempty (T ≅ coneRotatedTriangle f) := by
  let K : DifferentialGradedModule.{u, v, v} A := (T.obj₃⟦(-1 : ℤ)⟧).as
  let L : DifferentialGradedModule.{u, v, v} A := T.obj₁.as
  let w' : (quotient A).obj K ⟶ (quotient A).obj L :=
    T.mor₃⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (HomotopyCategory.{u, v, v} A) (1 : ℤ) (-1) (by norm_num)).hom.app
        T.obj₁
  let f : K ⟶ L := (quotient A).preimage w'
  refine ⟨K, L, f, ?_⟩
  let e₁ : T.obj₃ ≅ (quotient A).obj (shift K) :=
    ((shiftFunctorCompIsoId (HomotopyCategory.{u, v, v} A) (-1 : ℤ) 1 (by norm_num)).app
      T.obj₃).symm ≪≫ eqToIso (shiftFunctor_obj A K)
  have hsq : e₁.hom ≫ (coneRotatedTriangle f).mor₃ = T.mor₃ ≫ (Iso.refl _).hom := by
    dsimp only [e₁, coneRotatedTriangle, Triangle.mk_mor₃, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, Iso.app_inv, Iso.refl_hom]
    rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Functor.map_preimage, Functor.map_comp, shift_shiftFunctorCompIsoId_hom_app,
      Category.comp_id]
    have hn := (shiftFunctorCompIsoId (HomotopyCategory.{u, v, v} A) (-1 : ℤ) 1
      (by norm_num)).hom.naturality T.mor₃
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn
    rw [hn, Iso.inv_hom_id_app_assoc]
  obtain ⟨e', -⟩ := exists_iso_of_arrow_iso _ _ (rot_of_distTriang _ (rot_of_distTriang _ hT))
    (rot_of_distTriang _ (rot_of_distTriang _ (coneRotatedTriangle_distinguished f)))
    (Arrow.isoMk e₁ (Iso.refl _) hsq)
  exact ⟨(rotate _ ⋙ rotate _).preimageIso e'⟩

end HomotopyCategory

end ConeTriangle

/-! ### Derived sections are weakly triangulated -/

section Chaotic

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective
attribute [local instance 10000]
  _root_.DifferentialGradedModule.instPretriangulatedHomotopyCategory'

variable {C : Type u} [Category.{u} C]

/-- The category `C` with the chaotic topology and the sheaf of commutative rings `O`, as a ringed
site. -/
abbrev chaoticRingedSite (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}) :
    AlgebraicGeometry.RingedSite.{u, u, u} :=
  ⟨C, ⊥, O⟩

variable {O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chaoticRingedSite O).O))

/-- The shift by `ℤ` on the homotopy category `K(Mod(A, d))` over the chaotic ringed site. -/
@[instance_reducible]
noncomputable instance chaoticHomotopyHasShift :
    HasShift (HomotopyCategory.{u, v, v} A) ℤ :=
  HomotopyCategory.instHasShift (X := chaoticRingedSite O) A

/-- The shift functors of `K(Mod(A, d))` over the chaotic ringed site are additive. -/
instance chaoticHomotopyShiftFunctorAdditive (n : ℤ) :
    (shiftFunctor (HomotopyCategory.{u, v, v} A) n).Additive :=
  HomotopyCategory.shiftFunctor_additive (X := chaoticRingedSite O) A n

/-- The pretriangulated structure of `K(Mod(A, d))` over the chaotic ringed site. -/
@[instance_reducible]
noncomputable instance chaoticHomotopyPretriangulated :
    Pretriangulated (HomotopyCategory.{u, v, v} A) :=
  HomotopyCategory.instPretriangulated (X := chaoticRingedSite O) A

/-- The homotopy category `K(Mod(A, d))` over the chaotic ringed site is triangulated. -/
instance chaoticHomotopyIsTriangulated : IsTriangulated (HomotopyCategory.{u, v, v} A) :=
  HomotopyCategory.instIsTriangulated (X := chaoticRingedSite O) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` over the chaotic ringed site are multiplicative. -/
instance chaoticQuasiIsomorphismsIsMultiplicative :
    (quasiIsomorphisms.{u, v, v} A).IsMultiplicative :=
  quasiIsomorphisms_isMultiplicative' (X := chaoticRingedSite O) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` over the chaotic ringed site have a left calculus
of fractions. -/
instance chaoticQuasiIsomorphismsHasLeftCalculusOfFractions :
    (quasiIsomorphisms.{u, v, v} A).HasLeftCalculusOfFractions :=
  quasiIsomorphisms_hasLeftCalculusOfFractions (X := chaoticRingedSite O) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` over the chaotic ringed site have a right calculus
of fractions. -/
instance chaoticQuasiIsomorphismsHasRightCalculusOfFractions :
    (quasiIsomorphisms.{u, v, v} A).HasRightCalculusOfFractions :=
  quasiIsomorphisms_hasRightCalculusOfFractions (X := chaoticRingedSite O) A

/-- The quasi-isomorphisms of `K(Mod(A, d))` over the chaotic ringed site are compatible with the
triangulation. -/
instance chaoticQuasiIsomorphismsIsCompatibleWithTriangulation :
    (quasiIsomorphisms.{u, v, v} A).IsCompatibleWithTriangulation :=
  quasiIsomorphisms_isCompatibleWithTriangulation (X := chaoticRingedSite O) A

/-- **Derived sections over an object of a chaotic site are weakly triangulated**: they carry
the first two morphisms of a distinguished triangle of `D(A, d)` to the first two morphisms of a
distinguished triangle of `D(A(U), d)`. -/
theorem derivedSections_isWeaklyTriangulated (U : Cᵒᵖ) :
    (derivedSections A U).IsWeaklyTriangulated := by
  rintro T ⟨T₀, e, hT₀⟩
  obtain ⟨K, L, f, ⟨e'⟩⟩ := HomotopyCategory.exists_iso_coneRotatedTriangle T₀ hT₀
  let E : T ≅ (toDerivedCategory A).mapTriangle.obj (coneRotatedTriangle f) :=
    e ≪≫ (toDerivedCategory A).mapTriangle.mapIso e'
  have hadm := (isAdmissibleShortExact_conePackage f).sectionMap U
  have hK : _root_.DifferentialGradedModule.associatedTriangle _ _ _ hadm ∈
      distTriang (_root_.DifferentialGradedModule.HomotopyCategory (A.sectionAlgebra U)) := by
    rw [_root_.DifferentialGradedModule.distinguishedTriangles_eq]
    exact _root_.DifferentialGradedModule.isDistinguishedTriangle_associatedTriangle _ _ _ hadm
  let φ := derivedSectionsIso A U
  let S := derivedSections A U
  have key : ∀ {X Y P Q : derivedCategory A} {X' Y' : DifferentialGradedModule.derivedCategory'
      (A.sectionAlgebra U)} (u : X ⟶ Y) (eP : X ≅ P) (eQ : Y ≅ Q) (m : P ⟶ Q) (φP : S.obj P ⟶ X')
      (φQ : S.obj Q ⟶ Y') (t : X' ⟶ Y'), u ≫ eQ.hom = eP.hom ≫ m → S.map m ≫ φQ = φP ≫ t →
      S.map u ≫ S.map eQ.hom ≫ φQ = (S.map eP.hom ≫ φP) ≫ t := by
    intro X Y P Q X' Y' u eP eQ m φP φQ t h hn
    rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, hn, Category.assoc]
  refine exists_distinguished_of_iso _ _ _
    ((_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.map_distinguished
      _ hK) (S.mapIso (Triangle.π₁.mapIso E) ≪≫ φ.app L)
    (S.mapIso (Triangle.π₂.mapIso E) ≪≫ φ.app (conePackage f).cone)
    (S.mapIso (Triangle.π₃.mapIso E) ≪≫ φ.app (shift K)) ?_ ?_
  · exact key _ _ _ _ _ _ _ E.hom.comm₁ (φ.hom.naturality _)
  · exact key _ _ _ _ _ _ _ E.hom.comm₂ (φ.hom.naturality _)

end Chaotic

end DifferentialGradedModule

end SheafOfModules

end
