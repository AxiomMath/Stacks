module

public import StacksFrontier.Cotangent.SheavesOfRings.PointStalkCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.HenselianStalkVanishing
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctorialityComp
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseFundamentalTriangle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedNaiveMapConormal

/-!
# The stalk of the first arrow of the fundamental triangle of a tower of sheaves of rings

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site and let `Φ` be a
point of the site. The first arrow of the triangle of Tag 08SZ is the canonical map
`L_{B/A} ⊗_B D ⟶ L_{D/A}` (`CategoryTheory.Sheaf.towerCotangentBaseChange`). This file computes
its stalk at `Φ`: through the interchange `(L_{B/A} ⊗_B D)_Φ ≅ D_Φ ⊗_{B_Φ} (L_{B/A})_Φ` of
Stacks 05V5 and the identification `(L_{B/A})_Φ ≅ L_{B_Φ/A_Φ}` of Tag 08T0
(`CategoryTheory.Sheaf.pointStalkCotangentComplexIso`), it is the ring-level map
`D_Φ ⊗_{B_Φ} L_{B_Φ/A_Φ} ⟶ L_{D_Φ/A_Φ}` of the tower of stalk rings, the functoriality map of
Tag 08PN after extension of scalars, which is the first displayed morphism of the fundamental
triangle of the stalk rings.

## Main definitions

* `CategoryTheory.Sheaf.stalkOneTmul`: the element `1 ⊗ m` of `D_Φ ⊗_{B_Φ} (L^n_{B/A})_Φ`.
* `CategoryTheory.Sheaf.pointStalkAlgHom`: the stalk map `B_Φ → D_Φ` as a map of
  `A_Φ`-algebras.

## Main results

* `CategoryTheory.Sheaf.towerCotangentUnit_f_eq`: the unit `L_{B/A} ⟶ L_{B/A} ⊗_B D` is, in every
  degree, the unit of extension–restriction of scalars.
* `CategoryTheory.Sheaf.stalkBaseChangedCotangentComplexIso_inv_one_tmul`: the interchange on
  `1 ⊗ m`.
* `CategoryTheory.Sheaf.stalk_towerCotangentBaseChange`: the stalk of the first arrow of
  Tag 08SZ is the first displayed morphism of the fundamental triangle of the stalk rings.

## References

* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- In every degree the unit `L_{B/A} ⟶ L_{B/A} ⊗_B D` is the unit of extension–restriction of
scalars followed by the identification of the degreewise extension of `L_{B/A}` with the first
vertex of Tag 08SZ. -/
theorem towerCotangentUnit_f_eq (n : ℤ) :
    (towerCotangentUnit.{u, v, w} J g h).f n =
      (towerExtendRestrictAdjunction.{u, v, w} J h).unit.app ((cotangentComplex J g).X n) ≫
        (squareRestrict.{u, v, w} J h).map
          ((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom.f n) := by
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨n.natAbs, by omega⟩
    rw [towerCotangentUnit_f, towerExtendScalarsCotangentComplexIso_hom_f, Functor.map_comp,
      ← Category.assoc, ← (towerExtendRestrictAdjunction.{u, v, w} J h).unit_naturality]
    rfl
  · have hZ : IsZero ((baseChangedCotangentComplex.{u, v, w} J g h).X n) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
        rw [show (ComplexShape.embeddingUpIntLE (0 : ℤ)).f i = -(i : ℤ) by simp]
        omega)
    exact ((squareRestrict.{u, v, w} J h).map_isZero hZ).eq_of_tgt _ _

section Stalk

variable [LocallySmall.{max u v w} C] (Φ : J.Point.{max u v w})

/-- The element `1 ⊗ m` of `D_Φ ⊗_{B_Φ} (L^n_{B/A})_Φ`. -/
def stalkOneTmul (n : ℤ)
    (m : (Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J g).X n)) :
    (ModuleCat.extendScalars (Stacks.SitePointBaseChange.stalkRingHom h.hom Φ)).obj
      ((Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J g).X n)) :=
  (1 : (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj D.obj) ⊗ₜ[
    (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj B.obj,
    Stacks.SitePointBaseChange.stalkRingHom h.hom Φ] m

/-- The interchange `(L_{B/A} ⊗_B D)_Φ ≅ D_Φ ⊗_{B_Φ} (L_{B/A})_Φ`, read backwards, carries
`1 ⊗ m` to the stalk of the unit `L_{B/A} ⟶ L_{B/A} ⊗_B D` applied to `m`. -/
theorem stalkBaseChangedCotangentComplexIso_inv_one_tmul (n : ℤ)
    (m : (Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J g).X n)) :
    (stalkBaseChangedCotangentComplexIso Φ g h).inv.f n (stalkOneTmul J g h Φ n m) =
      (show (((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (baseChangedCotangentComplex.{u, v, w} J g h)).X n from
        (Stacks.sheafModuleFiberOfCommRing Φ B).map ((towerCotangentUnit.{u, v, w} J g h).f n)
          m) := by
  have e₁ := Stacks.Sheaves.StalkPullback.unit_square_app Φ h.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property
    ((cotangentComplex J g).X n) m
  show (Stacks.sheafModuleFiberOfCommRing Φ D).map
      ((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom.f n)
      ((Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso Φ h.hom
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property).inv.app
          ((cotangentComplex J g).X n) (stalkOneTmul J g h Φ n m)) = _
  refine (congrArg ((Stacks.sheafModuleFiberOfCommRing Φ D).map
      ((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom.f n)) e₁).trans ?_
  dsimp only
  rw [towerCotangentUnit_f_eq]
  exact (ConcreteCategory.congr_hom (Functor.map_comp (Stacks.sheafModuleFiberOfCommRing Φ B)
    ((towerExtendRestrictAdjunction.{u, v, w} J h).unit.app ((cotangentComplex J g).X n))
    ((squareRestrict.{u, v, w} J h).map
      ((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom.f n))) m).symm

attribute [local instance] moduleOfSections in
/-- Read through the interchange and the identifications of Tag 08T0, the stalk at `Φ` of
`L_{B/A} ⊗_B D ⟶ L_{D/A}` carries `1 ⊗ m` to the image of `m` under the map of cotangent
complexes of the square of stalk maps `(𝟙, B_Φ → D_Φ)`. -/
theorem pointStalkCotangentComplexIso_towerCotangentBaseChange_one_tmul (n : ℤ) (U : C)
    (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J g (op U))).X n) :
    (pointStalkCotangentComplexIso J Φ (g ≫ h)).hom.f n
        ((Stacks.sheafModuleFiberOfCommRing Φ D).map
            ((towerCotangentBaseChange.{u, v, w} J g h).f n)
          ((stalkBaseChangedCotangentComplexIso Φ g h).inv.f n
            (stalkOneTmul J g h Φ n (pointCotangentGerm J Φ g n U x s)))) =
      (CommAlgCat.cotangentComplexAbMap (pointStalkSquare J Φ g (𝟙 A) h (by simp))).f n
        ((CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ g U x)).f n s) := by
  rw [stalkBaseChangedCotangentComplexIso_inv_one_tmul]
  have e₁ := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (towerCotangentUnit_comp_towerCotangentBaseChange.{u, v, w} J g h)
  have e₂ : (Stacks.sheafModuleFiberOfCommRing Φ D).map
      ((towerCotangentBaseChange.{u, v, w} J g h).f n)
      ((Stacks.sheafModuleFiberOfCommRing Φ B).map ((towerCotangentUnit.{u, v, w} J g h).f n)
        (pointCotangentGerm J Φ g n U x s)) =
      (Stacks.sheafModuleFiberOfCommRing Φ B).map
        ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f n)
        (pointCotangentGerm J Φ g n U x s) := by
    rw [← e₁, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    exact (ConcreteCategory.congr_hom (Functor.map_comp (Stacks.sheafModuleFiberOfCommRing Φ B)
      ((towerCotangentUnit.{u, v, w} J g h).f n)
      ((squareRestrict.{u, v, w} J h).map ((towerCotangentBaseChange.{u, v, w} J g h).f n)))
        (pointCotangentGerm J Φ g n U x s)).symm
  refine (congrArg ((pointStalkCotangentComplexIso J Φ (g ≫ h)).hom.f n) e₂).trans ?_
  rw [sheafModuleFiberOfCommRing_map_squareCotangentComplexMap_germ]
  refine (pointStalkCotangentComplexIso_hom_germ J Φ (g ≫ h) n U x _).trans ?_
  exact (cotangentComplexAbMap_pointGermSquare_pointStalkSquare J Φ g (𝟙 A) h _ U x n s).symm

/-- The stalk map `B_Φ → D_Φ` of `h`, as a homomorphism of `A_Φ`-algebras. -/
def pointStalkAlgHom : pointStalkAlgebra J Φ g ⟶ pointStalkAlgebra J Φ (g ≫ h) :=
  letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
      ((Φ.presheafFiber (A := CommRingCat)).obj B.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map g.hom).hom.toAlgebra
  letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
      ((Φ.presheafFiber (A := CommRingCat)).obj D.obj) :=
    ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom.toAlgebra
  CommAlgCat.ofHom (R := (Φ.presheafFiber (A := CommRingCat)).obj A.obj)
    (X := (Φ.presheafFiber (A := CommRingCat)).obj B.obj)
    (Y := (Φ.presheafFiber (A := CommRingCat)).obj D.obj)
    { toRingHom := Stacks.SitePointBaseChange.stalkRingHom h.hom Φ
      commutes' := fun z => by
        change ((Φ.presheafFiber (A := CommRingCat)).map g.hom ≫
          (Φ.presheafFiber (A := CommRingCat)).map h.hom).hom z =
            ((Φ.presheafFiber (A := CommRingCat)).map (g ≫ h).hom).hom z
        rw [← Functor.map_comp]
        rfl }

omit [LocallySmall.{max u v w} C] in
/-- The square of stalk maps of `(𝟙 A, h)` is the square of the algebra map `B_Φ → D_Φ`. -/
theorem pointStalkSquare_id_eq_idSquare :
    pointStalkSquare J Φ g (𝟙 A) h (Category.id_comp _).symm =
      CommAlgCat.idSquare (pointStalkAlgHom J g h Φ) := by
  refine (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr ⟨?_, rfl⟩
  show ((Φ.presheafFiber (A := CommRingCat)).map (𝟙 A.obj)).hom = RingHom.id _
  rw [Functor.map_id]
  rfl

/-- Through the interchange `(L_{B/A} ⊗_B D)_Φ ≅ D_Φ ⊗_{B_Φ} (L_{B/A})_Φ` and the
identifications of Tag 08T0, the stalk at `Φ` of the first arrow `L_{B/A} ⊗_B D ⟶ L_{D/A}` of
the triangle of Tag 08SZ is the functoriality map `D_Φ ⊗_{B_Φ} L_{B_Φ/A_Φ} ⟶ L_{D_Φ/A_Φ}` of
Tag 08PN after extension of scalars, the first displayed morphism of the fundamental triangle of
the stalk rings `A_Φ → B_Φ → D_Φ`. -/
theorem stalk_towerCotangentBaseChange :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
        (pointStalkAlgebra J Φ (g ≫ h)) := CommAlgCat.algebra _
    (stalkBaseChangedCotangentComplexIso Φ g h).inv ≫
        ((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (towerCotangentBaseChange.{u, v, w} J g h) ≫
        (pointStalkCotangentComplexIso J Φ (g ≫ h)).hom =
      ((ModuleCat.extendScalars
          (Stacks.SitePointBaseChange.stalkRingHom h.hom Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (pointStalkCotangentComplexIso J Φ g).hom ≫
        CommAlgCat.cotangentExtendScalarsComplexMap
          (A := (Φ.presheafFiber (A := CommRingCat)).obj A.obj)
          (A' := (Φ.presheafFiber (A := CommRingCat)).obj A.obj) (B := pointStalkAlgebra J Φ g)
          (B' := pointStalkAlgebra J Φ (g ≫ h)) (pointStalkAlgHom J g h Φ).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.ExtendScalars.hom_ext fun m => ?_
  obtain ⟨U, x, s, rfl⟩ := exists_pointCotangentGerm_eq J Φ g n m
  refine (pointStalkCotangentComplexIso_towerCotangentBaseChange_one_tmul J g h Φ n U x s).trans ?_
  refine Eq.trans ?_ (CommAlgCat.cotangentExtendScalarsComplexMap_one_tmul
    (pointStalkAlgHom J g h Φ) n _).symm
  rw [pointStalkSquare_id_eq_idSquare, pointStalkCotangentComplexIso_hom_germ]
  rfl

end Stalk

end CategoryTheory.Sheaf

end
