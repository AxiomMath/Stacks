module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSiteTopoi
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckFunctorFrom

/-!
# The structure sheaf of a simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S` and `U_étale` its
small étale site. An object of `U_étale` lies in some simplicial degree `n` and is realized by an
algebraic space étale over `U_n`; a morphism of `U_étale` over `φ : [m] → [n]` is realized by a
morphism of algebraic spaces over `U(φ) : U_n → U_m`. Assigning to an object the ring of global
regular functions on its realization is a sheaf of rings `𝒪` on `U_étale`, the *structure sheaf of
the simplicial algebraic space*: its restriction to degree `n` is, through the realization, the
structure sheaf of `U_{n, spaces, étale}`, and it is a sheaf because the covering families of
`U_étale` lie in a single degree (Section 0DE7).

## Main definitions

* `AlgebraicGeometry.Space.etaleTotalToSpaces`: the realization functor from `U_étale` to
  algebraic spaces.
* `AlgebraicGeometry.Space.etaleStructureSheaf`: the structure sheaf `𝒪` of `U`.
* `AlgebraicGeometry.Space.etaleStructurePresheafRestrictIso`: the restriction of `𝒪` to degree
  `n` is the structure sheaf of `U_n`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor

universe u

/-- The unitor of the total pseudofunctor of a simplicial site is, at every object, the
`eqToHom` of the unit law of the underlying cosimplicial diagram of categories. -/
lemma CategoryTheory.SimplicialSite.totalPseudofunctor_mapId_app (C : SimplicialSite.{u})
    (n : SimplexCategoryᵒᵖ) (y : C.underlying.obj n.unop) :
    (C.totalPseudofunctor.mapId ⟨op n⟩).hom.toNatTrans.app y =
      eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (C.underlying.map_id n.unop)) y) := by
  simp [SimplicialSite.totalPseudofunctor]
  rfl

/-- The compositor of the total pseudofunctor of a simplicial site is, at every object, the
`eqToHom` of the composition law of the underlying cosimplicial diagram of categories. -/
lemma CategoryTheory.SimplicialSite.totalPseudofunctor_mapComp_app (C : SimplicialSite.{u})
    {k m n : SimplexCategoryᵒᵖ} (f : k ⟶ m) (g : m ⟶ n) (y : C.underlying.obj n.unop) :
    (C.totalPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app y =
      eqToHom (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor (C.underlying.map_comp g.unop f.unop)) y) := by
  simp [SimplicialSite.totalPseudofunctor]
  rfl

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent

/-- The comparison maps between realizations, as a natural transformation: the realization of
the transition of `y` along `ψ` maps to the realization of `y` over `U(ψ)`. -/
def realizeComparison {n k : SimplexCategory} (ψ : n ⟶ k) :
    transition (A := A) ψ ⋙ realizeFunctor k ⋙ SpacesEtale.toSpaces B S hS (A.left.obj (op k)) ⟶
      realizeFunctor n ⋙ SpacesEtale.toSpaces B S hS (A.left.obj (op n)) where
  app y := comparison ψ y
  naturality _ _ f := transition_map_hom_comp ψ f

variable {A} in
/-- The comparison along an identity is the identity, read as an `eqToHom`. -/
lemma comparison_id_eq_eqToHom {n : SimplexCategory} (y : Index A n)
    (h : (realize (y.push (𝟙 n))).obj.left = (realize y).obj.left) :
    comparison (𝟙 n) y = eqToHom h := by
  rcases y with V | ⟨m, φ, V⟩
  · exact (comparison_id_inl V).trans (eqToHom_refl _ _).symm
  · exact (comparison_id_inr φ V).trans (eqToHom_refl _ _).symm

variable {A} in
/-- The comparison along a composite is the composite of the comparisons, up to the
identification of the iterated transition with the transition along the composite. -/
lemma comparison_comp_eq {n k l : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l) (y : Index A n)
    (h : (realize (y.push (ψ ≫ χ))).obj.left = (realize ((y.push ψ).push χ)).obj.left) :
    comparison (ψ ≫ χ) y = eqToHom h ≫ comparison χ (y.push ψ) ≫ comparison ψ y := by
  rcases y with V | ⟨m, φ, V⟩
  · exact (comparison_comp_inl ψ χ V).trans
      ((Category.id_comp _).symm.trans (congrArg (· ≫ _) (eqToHom_refl _ _).symm))
  · exact (comparison_comp_inr ψ χ φ V).trans
      ((Category.id_comp _).symm.trans (congrArg (· ≫ _) (eqToHom_refl _ _).symm))

/-- A functor sends a morphism equal to an `eqToHom` to the `eqToHom` of the image objects. -/
private theorem eqToHom_eq_map_of_eq_eqToHom {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b : C} (f : a ⟶ b) (h : a = b) (hf : f = eqToHom h) :
    eqToHom (congrArg F.obj h) = F.map f := by
  subst h hf
  simp

/-- The unit law for the comparison maps between realizations. -/
theorem realizeComparison_id (n : SimplexCategoryᵒᵖ) :
    realizeComparison A (𝟙 n).unop =
      Functor.whiskerRight ((etaleSimplicialSite A).totalPseudofunctor.mapId ⟨op n⟩).hom.toNatTrans
        (realizeFunctor (A := A) n.unop ⋙
          SpacesEtale.toSpaces B S hS (A.left.obj (op n.unop))) := by
  refine NatTrans.ext (funext fun y => ?_)
  exact (comparison_id_eq_eqToHom y _).trans (eqToHom_eq_map_of_eq_eqToHom
    (realizeFunctor (A := A) n.unop ⋙ SpacesEtale.toSpaces B S hS _) _ _
    (SimplicialSite.totalPseudofunctor_mapId_app (etaleSimplicialSite A) n y))

/-- The cocycle law for the comparison maps between realizations. -/
theorem realizeComparison_comp {k m n : SimplexCategoryᵒᵖ} (f : k ⟶ m) (g : m ⟶ n) :
    realizeComparison A (f ≫ g).unop =
      Functor.whiskerRight
          ((etaleSimplicialSite A).totalPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans
          (realizeFunctor (A := A) k.unop ⋙ SpacesEtale.toSpaces B S hS (A.left.obj (op k.unop))) ≫
        ((etaleSimplicialSite A).totalPseudofunctor.map g.op.toLoc).toFunctor.whiskerLeft
          (realizeComparison A f.unop) ≫
        realizeComparison A g.unop := by
  refine NatTrans.ext (funext fun y => ?_)
  exact (comparison_comp_eq g.unop f.unop y _).trans
    (congrArg (· ≫ comparison f.unop (y.push g.unop) ≫ comparison g.unop y)
      (eqToHom_eq_map_of_eq_eqToHom
        (realizeFunctor (A := A) k.unop ⋙ SpacesEtale.toSpaces B S hS _) _ _
        (SimplicialSite.totalPseudofunctor_mapComp_app (etaleSimplicialSite A) f g y)))

/-- **The realization functor of `U_étale`.** An object of `U_étale` in degree `n` goes to the
algebraic space realizing it, étale over `U_n`, and a morphism over `φ` to the morphism of
realizations over `U(φ)`. -/
def etaleTotalToSpaces :
    CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor ⥤ AlgebraicSpaces B S hS :=
  CoGrothendieck.functorFrom
    (fun n => realizeFunctor (A := A) n.unop ⋙ SpacesEtale.toSpaces B S hS _)
    (fun {_ _} f => realizeComparison A f.unop) (realizeComparison_id A)
    (fun f g => realizeComparison_comp A f g)

/-- On the objects of a single degree `n`, the realization functor of `U_étale` is the
realization of the degree-`n` site. -/
def etaleTotalToSpacesιIso (n : SimplexCategoryᵒᵖ) :
    CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor n ⋙ etaleTotalToSpaces A ≅
      realizeFunctor (A := A) n.unop ⋙ SpacesEtale.toSpaces B S hS _ :=
  CoGrothendieck.ιCompFunctorFrom _ _ (realizeComparison_id A)
    (fun f g => realizeComparison_comp A f g) n

/-- The structure presheaf of the simplicial algebraic space on `U_étale`: global regular
functions on the realization of an object. -/
def etaleStructurePresheaf :
    (CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (etaleTotalToSpaces A).op ⋙ globalFunctionsPresheaf B S hS

/-- **The restriction of `𝒪` to degree `n` is the structure sheaf of `U_n`.** Restricted to the
objects of degree `n`, the structure presheaf of `U` is the structure sheaf of
`U_{n, spaces, étale}` read through the realization. -/
def etaleStructurePresheafRestrictIso (n : SimplexCategoryᵒᵖ) :
    (CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor n).op ⋙
        etaleStructurePresheaf A ≅
      (realizeFunctor (A := A) n.unop).op ⋙
        SpacesEtale.structurePresheaf B S hS (A.left.obj (op n.unop)) :=
  Functor.isoWhiskerRight (NatIso.op (etaleTotalToSpacesιIso A n)).symm
    (globalFunctionsPresheaf B S hS)

/-- The structure presheaf of `U` is a sheaf: the covering families of `U_étale` lie in a single
simplicial degree, where it is the structure sheaf of `U_n` read through the realization, which
is continuous. -/
theorem etaleStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (etaleSituation A).totalTopology (etaleStructurePresheaf A) := by
  refine (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat.{u + 1})).2 ?_
  refine (isSheaf_iff_isSheaf_of_type _ _).2 ?_
  have : (etaleSimplicialSite A).totalCoverage.HasPullbacks :=
    (etaleSimplicialSite A).totalCoverage_hasPullbacks
  have : (etaleSimplicialSite A).totalCoverage.IsStableUnderBaseChange :=
    (etaleSimplicialSite A).totalCoverage_isStableUnderBaseChange
  refine (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange
    (J := (etaleSimplicialSite A).totalCoverage) _).2 ?_
  rintro X R ⟨T, hT, rfl⟩
  refine Presieve.isSheafFor_map _ _ _ ?_
  refine Presieve.isSheafFor_iso
    (Functor.isoWhiskerRight (etaleStructurePresheafRestrictIso A X.base)
      (forget CommRingCat.{u + 1})).symm ?_
  refine (Presieve.isSheafFor_iff_generate T).2 ?_
  have h := Functor.op_comp_isSheaf (realizeFunctor (A := A) X.base.unop)
    (precoverage (A := A) X.base.unop).toGrothendieck
    (SpacesEtale.topology B S hS (A.left.obj (op X.base.unop)))
    (SpacesEtale.structureSheaf B S hS (A.left.obj (op X.base.unop)))
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat.{u + 1})).1 h) _
    (Precoverage.generate_mem_toGrothendieck hT)

/-- **Section 0DE7, the structure sheaf.** The sheaf of rings `𝒪` on the small étale site of the
simplicial algebraic space, whose restriction to degree `n` is the structure sheaf of `U_n`
(`etaleStructurePresheafRestrictIso`). -/
def etaleStructureSheaf : Sheaf (etaleSituation A).totalTopology CommRingCat.{u + 1} :=
  ⟨etaleStructurePresheaf A, etaleStructurePresheaf_isSheaf A⟩

end AlgebraicGeometry.Space

end
