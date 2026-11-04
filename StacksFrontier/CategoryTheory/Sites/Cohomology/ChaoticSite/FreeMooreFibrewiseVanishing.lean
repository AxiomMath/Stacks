module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.RepresentableAcyclicity
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy
public import StacksFrontier.Homology.HomologyColimit

/-!
# The free Moore complex of a simplicial set with contractible fibres over a set

Let `φ : S ⟶ K` be a morphism from a simplicial set to the constant simplicial set on a type `K`
such that every fibre `φ⁻¹(k)` is homotopy equivalent to a point. Then the Moore complex of the
free simplicial abelian group `ℤ[S]` has no homology in positive degrees.

## Main definitions

* `Stacks.ChaoticSite.constFibre`: the fibre `φ⁻¹(k)`, a simplicial subset of `S`.
* `Stacks.ChaoticSite.constFibreι`: the inclusion of `φ⁻¹(k)` into `S`.
* `Stacks.ChaoticSite.isColimitConstFibreCofan`: in each degree, `S` is the disjoint union of the
  fibres of `φ`.
* `Stacks.ChaoticSite.isColimitFreeMooreConstFibreCofan`: the Moore complex of `ℤ[S]` is the
  direct sum of those of the `ℤ[φ⁻¹(k)]`.

## Main results

* `Stacks.ChaoticSite.isZero_homology_freeMooreComplex_of_homotopyEquivalences`: a simplicial set
  homotopy equivalent to a point has the homology of a point, with the sections of the free
  abelian groups in any universe containing that of the simplicial set.
* `Stacks.ChaoticSite.isZero_homology_freeMooreComplex_of_constFibre`: the vanishing above.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.ChaoticSite

universe v t

variable {S : SimplicialObject (Type v)} {K : Type v}
  (φ : S ⟶ (Functor.const SimplexCategoryᵒᵖ).obj K)

/-- The fibre `φ⁻¹(k)` of a morphism to a constant simplicial set: the simplicial subset of `S`
of the simplices lying over `k`. -/
def constFibre (k : K) : SimplicialObject (Type v) where
  obj n := { x : S.obj n // φ.app n x = k }
  map {n m} f := TypeCat.ofHom fun (x : { x : S.obj n // φ.app n x = k }) =>
    (⟨S.map f x.1, by
      have h := ConcreteCategory.congr_hom (φ.naturality f) x.1
      simp only [Functor.const_obj_obj, Functor.const_obj_map, types_comp_apply,
        types_id_apply] at h
      exact h.trans x.2⟩ : { x : S.obj m // φ.app m x = k })
  map_id n := by
    ext x
    simp
  map_comp {n m l} f g := by
    ext x
    simp

/-- The inclusion of the fibre `φ⁻¹(k)` into `S`. -/
def constFibreι (k : K) : constFibre φ k ⟶ S where
  app n := TypeCat.ofHom fun (x : { x : S.obj n // φ.app n x = k }) => x.1

/-- In each degree, `S` is the disjoint union of the fibres of `φ`. -/
def isColimitConstFibreCofan (n : SimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk (S.obj n) fun k => (constFibreι φ k).app n) :=
  Cofan.IsColimit.mk _
    (fun c => TypeCat.ofHom fun (x : S.obj n) =>
      c.inj (φ.app n x) (⟨x, rfl⟩ : (constFibre φ (φ.app n x)).obj n))
    (fun c k => by
      ext ⟨x, hx⟩
      subst hx
      rfl)
    (fun c m hm => by
      ext x
      exact ConcreteCategory.congr_hom (hm (φ.app n x))
        (⟨x, rfl⟩ : (constFibre φ (φ.app n x)).obj n))

/-- The free simplicial abelian group on `S` (with sections lifted to the universe `max v t`)
has as Moore complex the direct sum of those of the fibres of `φ`. -/
def isColimitFreeMooreConstFibreCofan :
    IsColimit (Cofan.mk ((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
        (S ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free))
      fun k => (alternatingFaceMapComplex AddCommGrpCat.{max v t}).map
        (Functor.whiskerRight (constFibreι φ k) (uliftFunctor.{t} ⋙ AddCommGrpCat.free))) := by
  have : PreservesColimitsOfSize.{v, v} AddCommGrpCat.free.{max v t} :=
    AddCommGrpCat.adj.{max v t}.leftAdjoint_preservesColimits
  refine HomologicalComplex.isColimitOfEval _ _ fun n => ?_
  exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm
    (isColimitCofanMkObjOfIsColimit (uliftFunctor.{t} ⋙ AddCommGrpCat.free) _ _
      (isColimitConstFibreCofan φ (op (SimplexCategory.mk n))))

/-- **The free Moore complex of a simplicial set homotopy equivalent to a point has no homology
in positive degrees**, with the sections lifted to any universe containing that of the simplicial
set. -/
theorem isZero_homology_freeMooreComplex_of_homotopyEquivalences {X : SimplicialObject (Type v)}
    {f : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1}}
    (hf : SimplicialObject.homotopyEquivalences (Type v) f) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
      (X ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free)).homology n) := by
  let e : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1} ⋙ uliftFunctor.{t} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{max v t + 1} :=
    Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso (Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit))
  have hf' : SimplicialObject.homotopyEquivalences (Type (max v t))
      ((Iso.refl _).hom ≫ Functor.whiskerRight f uliftFunctor.{t} ≫ e.hom) :=
    CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp_iso _ _ _
      (CategoryTheory.SimplicialObject.homotopyEquivalences_whiskering_map uliftFunctor.{t} hf)
  refine IsZero.of_iso ?_ (freeMooreComplexHomologyIsoOfHomotopyEquiv hf' n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ChainComplex.alternatingConst_exactAt _ n (Nat.pos_iff_ne_zero.mp hn)

/-- **The free Moore complex of a simplicial set with contractible fibres over a set has no
homology in positive degrees.** Let `φ : S ⟶ K` be a morphism to the constant simplicial set on
a type `K` such that every fibre `φ⁻¹(k)` is homotopy equivalent to a point. Then the Moore
complex of the free simplicial abelian group on `S` is acyclic in positive degrees. -/
theorem isZero_homology_freeMooreComplex_of_constFibre
    (hφ : ∀ k, ∃ f : constFibre φ k ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1},
      SimplicialObject.homotopyEquivalences (Type v) f) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat.{max v t}).obj
      (S ⋙ uliftFunctor.{t} ⋙ AddCommGrpCat.free)).homology n) := by
  have : AB4OfSize.{v} AddCommGrpCat.{max v t} := AB4OfSize_shrink.{v, t} _
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := AddCommGrpCat.{max v t}) (J := Discrete K) (ComplexShape.down ℕ) n
  have hc := isColimitOfPreserves
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max v t} (ComplexShape.down ℕ) n)
    (isColimitFreeMooreConstFibreCofan.{v, t} φ)
  rw [IsZero.iff_id_eq_zero]
  refine hc.hom_ext fun ⟨k⟩ => ?_
  obtain ⟨f, hf⟩ := hφ k
  exact (isZero_homology_freeMooreComplex_of_homotopyEquivalences.{v, t} hf n hn).eq_of_src _ _

end Stacks.ChaoticSite

end
