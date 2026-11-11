module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness
public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated

/-!
# Right acyclic objects when `RF` is everywhere defined

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, and assume that the right
derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is *everywhere defined* in the sense of the source: for every
object `X` of `K⁺(𝒜)` the ind-object `X/Qis⁺(𝒜) ⟶ D⁺(ℬ)`, `(s : X ⟶ X') ↦ F(X')` is essentially
constant (`CategoryTheory.Functor.IsRightDerivable`, [Stacks, Tag 05SV]). No injective objects are
assumed. Writing `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])` ([Stacks, Tag 015A]), this file proves the
characterization of right acyclic objects ([Stacks, Tag 015C]): `A` is right acyclic for `F` if and
only if `F(A) ⟶ R ⁰ F(A)` is an isomorphism and `R ⁱ F(A) = 0` for `i > 0`, the first condition
being automatic for a left exact `F`.

The two inputs from [Stacks, Tag 05TD] are proved here for an everywhere defined `RF`, by the
source's own argument: the value `RF(A[0])` is a retract of `F(L)` for a quasi-isomorphism
`A[0] ⟶ L`, and such an `L` may be replaced by its truncation `τ_{≥ 0}L`, a complex concentrated in
degrees `≥ 0`. Hence `R ⁱ F(A) = 0` for `i < 0`; and for a left exact `F` the map
`H ⁰(F(A[0])) ⟶ H ⁰(F(L))` is an isomorphism for every such `L`, which makes `F(A) ⟶ R ⁰ F(A)` both
a split monomorphism and an epimorphism.

## Main definitions

* `CategoryTheory.Functor.totalRightDerivedPlusHomology`: the functor
  `R ⁱ F = H ⁱ ∘ RF ∘ (·[0]) : 𝒜 ⥤ ℬ` for the right derived functor `RF` of `K⁺(F) ⋙ Q⁺`, wherever
  that derived functor exists.

## Main results

* `CategoryTheory.Functor.isZero_homologyFunctor_obj_of_isRightDerivable`: `R ⁱ F(A) = 0` for
  `i < 0`.
* `CategoryTheory.Functor.isIso_homologyFunctor_map_app_of_isRightDerivable`: for a left exact
  `F`, the canonical map `F(A) ⟶ R ⁰ F(A)` is an isomorphism.
* `CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_totalRightDerivedPlusHomology`:
  [Stacks, Tag 015C].

## Implementation notes

The source's hypothesis that `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be everywhere defined is
`(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
(HomotopyCategory.Plus.quasiIso 𝒜)`. It implies that Mathlib's right derived functor of
`K⁺(F) ⋙ Q⁺` exists (`Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable`), and its
value at `X` is the source's value `RF(X)`: the cocone `Functor.derivedUnitCocone` is a value in the
sense of [Stacks, Tag 05S9] (`Functor.isRightDerivedValueAt_derivedUnitCocone`). The statements
also carry the instance `HasRightDerivedFunctor`, which that hypothesis implies, because the
predicate `Functor.rightAcyclic` of [Stacks, Tag 0157] and the functor `RF` are named through it.

## References

* [Stacks, Tag 015C]
* [Stacks, Tag 05TD], parts (1) and (3), for an everywhere defined `RF`
* [Stacks, Tag 05SV], [Stacks, Tag 05S9]
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

open _root_.DerivedCategory

section Complexes

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A left exact functor preserves quasi-isomorphisms in degree `0` between complexes concentrated
in degrees `≥ 0`: in degree `0` the homology of such a complex is the kernel of its first
differential, which a left exact functor preserves. -/
private lemma quasiIsoAt_map_zero_of_isStrictlyGE (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℤ} (g : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] [hg : QuasiIsoAt g 0] :
    QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) 0 := by
  have hK : F.PreservesLeftHomologyOf
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).obj K) :=
    F.preservesLeftHomology_of_zero_f _
      ((K.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _)
  have hL : F.PreservesLeftHomologyOf
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).obj L) :=
    F.preservesLeftHomology_of_zero_f _
      ((L.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _)
  have := (quasiIsoAt_iff g 0).1 hg
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map g)

/-- A retract of a zero object is a zero object. -/
private lemma isZero_of_retract {X Y : D} (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X)
    (hY : IsZero Y) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, ← h, hY.eq_of_src p 0, Limits.comp_zero]

end Complexes

section Homology

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- The homology of `Q⁺(K)` is the homology of `K` in the homotopy category. -/
private noncomputable def qhCompHomologyFunctorIso (n : ℤ) :
    Plus.Qh ⋙ Plus.homologyFunctor D n ≅
      HomotopyCategory.Plus.ι D ⋙ HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n :=
  (Functor.associator Plus.Qh Plus.ι (DerivedCategory.homologyFunctor D n)).symm ≪≫
    Functor.isoWhiskerRight (Plus.QhCompιIsoιCompQh D) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh D n)

end Homology

section Truncation

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]

/-- The complex `A[0]` of `K⁺(𝒜)` is concentrated in degrees `≥ 0`. -/
private lemma isStrictlyGE_singleFunctor_obj (A : C) :
    CochainComplex.IsStrictlyGE ((HomotopyCategory.Plus.singleFunctor C 0).obj A).obj.as 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A) 0)

/-- Every index `s : A[0] ⟶ L` of the ind-object defining `RF(A[0])` maps to an index whose target
is concentrated in degrees `≥ 0`: `L` is cohomologically `≥ 0` because it is quasi-isomorphic to
`A[0]`, so `L ⟶ τ_{≥ 0}L` is a quasi-isomorphism. -/
private lemma exists_hom_isStrictlyGE (A : C)
    (t : (HomotopyCategory.Plus.quasiIso C).Under ⊤
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) :
    ∃ (t' : (HomotopyCategory.Plus.quasiIso C).Under ⊤
        ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) (_ : t ⟶ t'),
      CochainComplex.IsStrictlyGE t'.right.obj.as 0 := by
  have := isStrictlyGE_singleFunctor_obj A
  obtain ⟨g, hg⟩ : ∃ g : ((HomotopyCategory.Plus.singleFunctor C 0).obj A).obj.as ⟶
      t.right.obj.as,
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g = t.hom.hom :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective t.hom.hom
  have hqg : QuasiIso g := by
    have h := t.prop
    rw [HomotopyCategory.Plus.quasiIso_iff, ← hg] at h
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 h
  have hK : CochainComplex.IsGE t.right.obj.as 0 :=
    (HomologicalComplex.isSupported_iff_of_quasiIso g (ComplexShape.embeddingUpIntGE 0)).1
      inferInstance
  let T : HomotopyCategory.Plus C :=
    plusObj (CochainComplex.truncGE t.right.obj.as 0) ⟨0, inferInstance⟩
  let π : t.right ⟶ T :=
    ObjectProperty.homMk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (CochainComplex.πTruncGE t.right.obj.as 0))
  have hπ : HomotopyCategory.Plus.quasiIso C π := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
      (CochainComplex.πTruncGE t.right.obj.as 0)).2
      ((CochainComplex.quasiIso_πTruncGE_iff t.right.obj.as 0).2 hK)
  exact ⟨MorphismProperty.Under.mk ⊤ (t.hom ≫ π)
      (MorphismProperty.comp_mem _ _ _ t.prop hπ),
    MorphismProperty.Under.homMk π rfl trivial,
    inferInstanceAs (CochainComplex.IsStrictlyGE (CochainComplex.truncGE t.right.obj.as 0) 0)⟩

/-- `F(L)` has no homology in negative degrees when `L` is concentrated in degrees `≥ 0`. -/
private lemma isZero_homologyFunctor_obj_map (P : HomotopyCategory.Plus C)
    [CochainComplex.IsStrictlyGE P.obj.as 0] (i : ℤ) (hi : i < 0) :
    IsZero ((Plus.homologyFunctor D i).obj
      ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj P)) := by
  have : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.obj.as) 0 := inferInstance
  have : ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj P).IsGE 0 :=
    isGE_Qh_obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.obj.as) ⟨0, this⟩ 0 this
  exact Plus.isZero_homology_of_isGE _ 0 i hi

/-- For a left exact `F`, a quasi-isomorphism `f : A[0] ⟶ L` onto a complex concentrated in
degrees `≥ 0` induces an isomorphism `H ⁰(F(A[0])) ⟶ H ⁰(F(L))`. -/
private lemma isIso_homologyFunctor_map_map [PreservesFiniteLimits F] (A : C)
    (P : HomotopyCategory.Plus C) [CochainComplex.IsStrictlyGE P.obj.as 0]
    (f : (HomotopyCategory.Plus.singleFunctor C 0).obj A ⟶ P)
    (hf : HomotopyCategory.Plus.quasiIso C f) :
    IsIso ((Plus.homologyFunctor D 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map f)) := by
  have := isStrictlyGE_singleFunctor_obj A
  obtain ⟨g, hg⟩ : ∃ g : ((HomotopyCategory.Plus.singleFunctor C 0).obj A).obj.as ⟶ P.obj.as,
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g = f.hom :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f.hom
  have hqg : QuasiIso g := by
    rw [HomotopyCategory.Plus.quasiIso_iff, ← hg] at hf
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hf
  have hFg := quasiIsoAt_map_zero_of_isStrictlyGE F g
  rw [quasiIsoAt_iff_isIso_homologyMap] at hFg
  have h₁ : IsIso ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) 0).map
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g))) :=
    (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) 0)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g)).2 hFg
  rw [← Functor.mapHomotopyCategory_map, hg] at h₁
  exact (NatIso.isIso_map_iff (qhCompHomologyFunctorIso 0) (F.mapHomotopyCategoryPlus.map f)).2 h₁

end Truncation

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
  (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]

/-- The coprojection at `(s : X ⟶ X')` of the value cocone `Functor.derivedUnitCocone`: `α` at
`X'` followed by the inverse of `RF(s)`. -/
private noncomputable def unitLeg (X : HomotopyCategory.Plus C)
    (s : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X) :
    (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj s.right ⟶ RF.obj (Plus.Qh.obj X) :=
  α.app s.right ≫ RF.map ((HomotopyCategory.Plus.quasiIso C).underIso Plus.Qh X s).inv

omit [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] in
/-- The coprojections `unitLeg` are compatible with the transition morphisms. -/
private lemma map_right_comp_unitLeg (X : HomotopyCategory.Plus C)
    {s t : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X} (v : s ⟶ t) :
    (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right ≫ unitLeg F RF α X t =
      unitLeg F RF α X s :=
  (derivedUnitCocone (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)
    (HomotopyCategory.Plus.quasiIso C) Plus.Qh RF α X).w v

omit [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] in
/-- The unit `α_X` is `F(s)` followed by the coprojection at `s`. -/
private lemma map_hom_comp_unitLeg (X : HomotopyCategory.Plus C)
    (s : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X) :
    (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map s.hom ≫ unitLeg F RF α X s = α.app X := by
  have h : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map s.hom ≫ α.app s.right =
      α.app X ≫ RF.map (Plus.Qh.map s.hom) := α.naturality s.hom
  rw [unitLeg, ← Category.assoc, h, Category.assoc, ← RF.map_comp,
    ← MorphismProperty.underIso_hom, Iso.hom_inv_id, RF.map_id]
  exact Category.comp_id _

/-- When `RF` is everywhere defined, `RF(X)` is the value of the essentially constant ind-object
`(s : X ⟶ X') ↦ F(X')` with coprojections `unitLeg`, in the sense of [Stacks, Tag 05S9]. -/
private lemma exists_unitLeg_retraction
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) (X : HomotopyCategory.Plus C) :
    ∃ (s₀ : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X)
      (r : RF.obj (Plus.Qh.obj X) ⟶ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj s₀.right),
      r ≫ unitLeg F RF α X s₀ = 𝟙 _ ∧
        ∀ s : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X,
          ∃ (t : (HomotopyCategory.Plus.quasiIso C).Under ⊤ X) (u : s ⟶ t) (v : s₀ ⟶ t),
            (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u.right =
              unitLeg F RF α X s ≫ r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right := by
  have : (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  obtain ⟨s₀, r, hr, hfac⟩ := isRightDerivedValueAt_derivedUnitCocone _ _ _ RF α hF X
  exact ⟨s₀, r, hr, hfac⟩

include α in
/-- **Part (1) of [Stacks, Tag 05TD] for an everywhere defined `RF`**: `R ⁱ F(A) = 0` for `i < 0`.
The value `RF(A[0])` is a retract of `F(L)` for a quasi-isomorphism `A[0] ⟶ L` which may be taken
with `L` concentrated in degrees `≥ 0`. -/
public lemma isZero_homologyFunctor_obj_of_isRightDerivable
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) (A : C) (i : ℤ) (hi : i < 0) :
    IsZero ((Plus.homologyFunctor D i).obj
      (RF.obj (Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj A)))) := by
  obtain ⟨s₀, r, hr, -⟩ := exists_unitLeg_retraction F RF α hF
    ((HomotopyCategory.Plus.singleFunctor C 0).obj A)
  obtain ⟨t, v, ht⟩ := exists_hom_isStrictlyGE A s₀
  have hret : (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right) ≫
      unitLeg F RF α _ t = 𝟙 _ := by
    rw [Category.assoc, map_right_comp_unitLeg, hr]
  refine isZero_of_retract ((Plus.homologyFunctor D i).map
      (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right))
    ((Plus.homologyFunctor D i).map (unitLeg F RF α _ t)) ?_
    (isZero_homologyFunctor_obj_map F t.right i hi)
  rw [← Functor.map_comp, hret, Functor.map_id]

/-- **Part (3), `⇐`, of [Stacks, Tag 05TD] for an everywhere defined `RF`**: for a left exact `F`,
the canonical map `F(A) ⟶ R ⁰ F(A)`, that is `H ⁰(α)` at `A[0]`, is an isomorphism.

`H ⁰(F(A[0])) ⟶ H ⁰(F(L))` is an isomorphism for every quasi-isomorphism `A[0] ⟶ L` with `L`
concentrated in degrees `≥ 0`. Essential constancy factors one such map through `H ⁰(α)`, which is
therefore a monomorphism, and writes `H ⁰(α)` as such a map followed by a split epimorphism. -/
public lemma isIso_homologyFunctor_map_app_of_isRightDerivable [PreservesFiniteLimits F]
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) (A : C) :
    IsIso ((Plus.homologyFunctor D 0).map
      (α.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) := by
  obtain ⟨s₀, r, hr, hfac⟩ := exists_unitLeg_retraction F RF α hF
    ((HomotopyCategory.Plus.singleFunctor C 0).obj A)
  -- `H ⁰(α)` is an epimorphism: it is `H ⁰(F(t))` followed by a split epimorphism.
  have hepi : Epi ((Plus.homologyFunctor D 0).map
      (α.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) := by
    obtain ⟨t, v, ht⟩ := exists_hom_isStrictlyGE A s₀
    have hret : (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right) ≫
        unitLeg F RF α _ t = 𝟙 _ := by
      rw [Category.assoc, map_right_comp_unitLeg, hr]
    have hsplit : IsSplitEpi ((Plus.homologyFunctor D 0).map (unitLeg F RF α _ t)) :=
      ⟨⟨(Plus.homologyFunctor D 0).map (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right),
        by rw [← Functor.map_comp, hret, Functor.map_id]⟩⟩
    have hiso := isIso_homologyFunctor_map_map F A t.right t.hom t.prop
    have e : (Plus.homologyFunctor D 0).map
        (α.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) =
        (Plus.homologyFunctor D 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t.hom) ≫
          (Plus.homologyFunctor D 0).map (unitLeg F RF α _ t) := by
      rw [← map_hom_comp_unitLeg F RF α _ t]
      exact (Plus.homologyFunctor D 0).map_comp _ _
    rw [e]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hiso) _
      (@IsSplitEpi.epi _ _ _ _ _ hsplit)
  -- `H ⁰(α)` is a monomorphism: `H ⁰(F(t₁))` factors through it.
  have hmono : Mono ((Plus.homologyFunctor D 0).map
      (α.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) := by
    obtain ⟨t, u, v, huv⟩ := hfac s₀
    obtain ⟨t₁, v₁, ht₁⟩ := exists_hom_isStrictlyGE A t
    have hfac₁ : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₁.hom =
        α.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A) ≫
          ((r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right) ≫
            (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right) := by
      calc (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₁.hom
          = (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map ((s₀.hom ≫ u.right) ≫ v₁.right) := by
            congr 1
            rw [MorphismProperty.Under.w u, MorphismProperty.Under.w v₁]
        _ = ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map s₀.hom ≫
              (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u.right) ≫
              (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right := by
            rw [Functor.map_comp, Functor.map_comp]
        _ = ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map s₀.hom ≫ unitLeg F RF α _ s₀ ≫
              r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right) ≫
              (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right := by
            rw [huv]
        _ = _ := by
            rw [← Category.assoc ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map s₀.hom),
              map_hom_comp_unitLeg]
            simp only [Category.assoc]
    have hiso := isIso_homologyFunctor_map_map F A t₁.right t₁.hom t₁.prop
    have e : (Plus.homologyFunctor D 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₁.hom) =
        (Plus.homologyFunctor D 0).map
          (α.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) ≫
          (Plus.homologyFunctor D 0).map
            ((r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v.right) ≫
              (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right) := by
      rw [hfac₁]
      exact (Plus.homologyFunctor D 0).map_comp _ _
    rw [e] at hiso
    exact @mono_of_mono _ _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hiso)
  exact isIso_of_mono_of_epi _

end General

section HigherRightDerived

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [(F.mapHomotopyCategoryPlus ⋙ Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso C)]

/-- The `i`-th right derived functor `R ⁱ F = H ⁱ ∘ RF : 𝒜 ⥤ ℬ` of an additive functor
`F : 𝒜 ⥤ ℬ` between abelian categories ([Stacks, Tag 015A]), where `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is the
right derived functor of `K⁺(F) ⋙ Q⁺` along `Q⁺ : K⁺(𝒜) ⥤ D⁺(𝒜)` with respect to the
quasi-isomorphisms, and `𝒜 → D⁺(𝒜)` sends an object to the complex concentrated in degree `0`.
Unlike `Functor.rightDerivedPlus`, no injective objects are assumed: only the existence of `RF`. -/
public noncomputable def totalRightDerivedPlusHomology (i : ℤ) : C ⥤ D :=
  Plus.singleFunctor C 0 ⋙
    (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
      (HomotopyCategory.Plus.quasiIso C) ⋙
    Plus.homologyFunctor D i

/-- `R ⁱ F(A)` is the `i`-th homology of the target of the unit of `RF` at `A[0]`. -/
private noncomputable def totalRightDerivedPlusHomologyObjIso (A : C) (i : ℤ) :
    (F.totalRightDerivedPlusHomology i).obj A ≅ (Plus.homologyFunctor D i).obj
      (((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
        (HomotopyCategory.Plus.quasiIso C)).obj
          (Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) :=
  (Plus.homologyFunctor D i).mapIso
    (((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)).mapIso ((singleFunctorPlusIsoCompQh 0).app A))

/-- **Characterization of right acyclic objects**, [StacksProject 015C].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories and assume that
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined, that is, `K⁺(F) ⋙ Q⁺` is right derivable with
respect to the quasi-isomorphisms of `K⁺(𝒜)` ([Stacks, Tag 05SV]); `RF` is its right derived
functor, with unit `α`, and `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`. Let `A` be an object of `𝒜`. Then
1. `A` is right acyclic for `F` if and only if the canonical map `F(A) ⟶ R ⁰ F(A)`, that is
   `H ⁰(α)` at `A[0]`, is an isomorphism and `R ⁱ F(A) = 0` for all `i > 0`, and
2. if `F` is left exact, then `A` is right acyclic for `F` if and only if `R ⁱ F(A) = 0` for
   all `i > 0`.

The instance `HasRightDerivedFunctor` follows from `hF`
(`Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable`); it names `RF` and the predicate
`Functor.rightAcyclic`. No injective objects are assumed; with enough injectives this is
`Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`. -/
@[stacks 015C "`RF` everywhere defined is `Functor.IsRightDerivable` of `K⁺(F) ⋙ Q⁺` (Tag 05SV); \
`R ⁱ F` is `Functor.totalRightDerivedPlusHomology`, and `F(A) ⟶ R ⁰ F(A)` is `H ⁰` of the unit \
of `RF` at `A[0]`"]
public theorem rightAcyclic_iff_isIso_and_isZero_totalRightDerivedPlusHomology
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) (A : C) :
    (F.rightAcyclic A ↔
        (IsIso ((Plus.homologyFunctor D 0).map
            (((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
              (HomotopyCategory.Plus.quasiIso C)).app
                ((HomotopyCategory.Plus.singleFunctor C 0).obj A))) ∧
          ∀ i > 0, IsZero ((F.totalRightDerivedPlusHomology i).obj A))) ∧
      (PreservesFiniteLimits F →
        (F.rightAcyclic A ↔ ∀ i > 0, IsZero ((F.totalRightDerivedPlusHomology i).obj A))) := by
  set RF := (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  set α := (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  set X := (HomotopyCategory.Plus.singleFunctor C 0).obj A
  have hsrc := isZero_homologyFunctor_obj_map_singleFunctor_obj F A
  have hneg := isZero_homologyFunctor_obj_of_isRightDerivable F RF α hF A
  have h₁ : F.rightAcyclic A ↔ (IsIso ((Plus.homologyFunctor D 0).map (α.app X)) ∧
      ∀ i > 0, IsZero ((F.totalRightDerivedPlusHomology i).obj A)) := by
    constructor
    · intro h
      have h' : IsIso (α.app X) := h
      refine ⟨inferInstance, fun i hi => ?_⟩
      exact IsZero.of_iso (IsZero.of_iso (hsrc i hi.ne')
        (asIso ((Plus.homologyFunctor D i).map (α.app X))).symm)
        (totalRightDerivedPlusHomologyObjIso F A i)
    · rintro ⟨h₀, hpos⟩
      change IsIso (α.app X)
      rw [Plus.isIso_iff]
      intro i
      rcases lt_trichotomy i 0 with hi | rfl | hi
      · exact (hsrc i hi.ne).isIso (hneg i hi) _
      · exact h₀
      · exact (hsrc i hi.ne').isIso
          (IsZero.of_iso (hpos i hi) (totalRightDerivedPlusHomologyObjIso F A i).symm) _
  refine ⟨h₁, fun hlex => ?_⟩
  rw [h₁]
  exact and_iff_right (isIso_homologyFunctor_map_app_of_isRightDerivable F RF α hF A)

end HigherRightDerived

end CategoryTheory.Functor

end
