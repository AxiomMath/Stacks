module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalConstructions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriek
public import StacksFrontier.CategoryTheory.Triangulated.Functor

/-!
# The homology of derived lower shriek as a homological δ-functor

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site, and let
`Lπ_! : D(Ab(C)) ⥤ D(Ab(D))` be the left derived lower-shriek functor of the induced morphism of
topoi. The family `F ↦ H^{-n}(Lπ_! F)`, `n ≥ 0`, is a homological δ-functor: a short exact
sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves on `C` gives the distinguished triangle
`F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[1]` of `D(Ab(C))`, its image under `Lπ_!` is distinguished, and the
connecting morphisms are those of the long exact homology sequence of that image.

## Main definitions

* `Stacks.Sites.FibredCategory.singleDeltaFunctorStructure`: the δ-functor structure on the
  functor `F ↦ F[0]` from an abelian category to its derived category, carried by the triangle
  of a short exact sequence.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekDeltaFunctorStructure`:
  the δ-functor structure on `F ↦ Lπ_!(F[0])`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyDeltaFunctor`:
  the family `F ↦ H^{-n}(Lπ_! F)` as a homological δ-functor. Its degree-`n` functor is
  `derivedAbelianLowerShriekHomology n`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.AbelianLowerShriekGeneratorsAcyclic`:
  `Lπ_!` carries every direct sum of the free abelian sheaves `j_{U!} ℤ_U` to an object with no
  cohomology in negative degrees.

## Main results

* `Stacks.Sites.FibredCategory.isLE_of_forall_hom_eq_zero`: an object of a pre-triangulated
  category with a t-structure which admits no nonzero morphism to an object of `D^{≥ n+1}`
  lies in `D^{≤ n}`.
* `Stacks.Sites.FibredCategory.isGE_mapDerivedCategory_obj`: the functor induced on derived
  categories by an exact functor of abelian categories preserves boundedness below.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.isLE_derivedAbelianLowerShriek_obj_single`:
  `Lπ_!(F[0])` is bounded above by `0`, i.e. `H^i(Lπ_! F) = 0` for `i > 0`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedAbelianLowerShriek_isTriangulated`:
  `Lπ_!` is an exact functor of triangulated categories.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.coeffaceable_derivedLowerShriekHomology`
  and `isUniversal_derivedLowerShriekHomology`: when `AbelianLowerShriekGeneratorsAcyclic` holds,
  the homological δ-functor is coeffaceable and universal.
* `abelianLowerShriekGeneratorsAcyclic_of_preservesFiniteLimits` and
  `isGE_derivedAbelianLowerShriek_obj_single_of_preservesFiniteLimits`, in the same namespace:
  `AbelianLowerShriekGeneratorsAcyclic` holds whenever lower shriek is exact.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0150](https://stacks.math.columbia.edu/tag/0150)
* [Stacks Project, Tag 0151](https://stacks.math.columbia.edu/tag/0151)
* [Stacks Project, Tag 05SR](https://stacks.math.columbia.edu/tag/05SR)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w t v u w₁ w₂ v₁ v₂ u₁ u₂

section TStructure

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- For a t-structure `t` and `n₀ + 1 = n₁`, an object with no nonzero morphism into an object
of `D^{≥ n₁}` lies in `D^{≤ n₀}`. -/
theorem isLE_of_forall_hom_eq_zero (t : TStructure D) (X : D) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    (hX : ∀ Y : D, t.IsGE Y n₁ → ∀ f : X ⟶ Y, f = 0) : t.IsLE X n₀ := by
  obtain ⟨A, B, hA, hB, f, g, k, hT⟩ := t.exists_triangle X n₀ n₁ hn
  have hAle : t.IsLE A n₀ := ⟨hA⟩
  have hBge : t.IsGE B n₁ := ⟨hB⟩
  have hshift : t.IsLE (A⟦(1 : ℤ)⟧) (n₀ - 1) := t.isLE_shift A n₀ 1 (n₀ - 1) (by ring)
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₃ _ hT (𝟙 B) (by simpa using hX B hBge g)
  have hBzero : IsZero B := by
    rw [IsZero.iff_id_eq_zero, hu,
      t.zero_of_isLE_of_isGE u (n₀ - 1) n₁ (by lia) hshift hBge, comp_zero]
  have hiso : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hBzero
  exact t.isLE_of_iso (asIso f) n₀

end TStructure

section MapDerivedCategory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- The functor induced on derived categories by an exact functor of abelian categories carries
`D^{≥ n}` into `D^{≥ n}`. -/
theorem isGE_mapDerivedCategory_obj (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (Y : DerivedCategory C₁) (n : ℤ) [Y.IsGE n] :
    (F.mapDerivedCategory.obj Y).IsGE n := by
  obtain ⟨K, _, ⟨e⟩⟩ := Y.exists_iso_Q_obj_of_isGE n
  have hstr : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ F.map_isZero (K.isZero_of_isStrictlyGE n i hi)
  have e₂ : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      F.mapDerivedCategory.obj Y :=
    (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e.symm
  exact DerivedCategory.TStructure.t.isGE_of_iso e₂ n

end MapDerivedCategory

section Single

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{t} A]

/-- The δ-functor structure on `F ↦ F[0]`: the connecting morphism of a
short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is `ShortComplex.ShortExact.singleδ`, and the
resulting triangle `F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[1]` is distinguished. -/
def singleDeltaFunctorStructure :
    (DerivedCategory.singleFunctor A 0).DeltaFunctorStructure A (DerivedCategory A) where
  δ hS := hS.singleδ
  distinguished hS := hS.singleTriangle_distinguished
  δ_naturality h₁ h₂ φ := (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃

end Single

section DeltaTriangleHom

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  {𝒟 : Type u₁} [Category.{v₁} 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] {G : 𝒜 ⥤ 𝒟}

/-- The morphism of triangles that a δ-functor attaches to a morphism of short exact
sequences: the functor applied to the three components. -/
def deltaFunctorMapTriangleHom (d : G.DeltaFunctorStructure 𝒜 𝒟) {S S' : ShortComplex 𝒜}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') :
    Triangle.mk (G.map S.f) (G.map S.g) (d.δ hS) ⟶
      Triangle.mk (G.map S'.f) (G.map S'.g) (d.δ hS') :=
  Triangle.homMk _ _ (G.map φ.τ₁) (G.map φ.τ₂) (G.map φ.τ₃)
    (by simpa using (congrArg G.map φ.comm₁₂).symm)
    (by simpa using (congrArg G.map φ.comm₂₃).symm)
    (d.δ_naturality hS hS' φ)

end DeltaTriangleHom

namespace FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
    (ComplexShape.up ℤ))]

/-- Derived restriction preserves boundedness below. -/
instance isGE_derivedAbelianInverseImage_obj
    (Y : DerivedCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC})) (n : ℤ)
    [Y.IsGE n] : (s.derivedAbelianInverseImage.obj Y).IsGE n :=
  isGE_mapDerivedCategory_obj _ Y n

/-- The commutation of `Lπ_!` with the shift, as the left adjoint of derived restriction. -/
@[instance_reducible]
def derivedAbelianLowerShriekCommShift (h : s.AbelianLowerShriekAcyclic) :
    s.derivedAbelianLowerShriek.CommShift ℤ :=
  (s.derivedAbelianLowerShriekAdjunction h).leftAdjointCommShift ℤ

/-- `Lπ_!` is an exact functor of triangulated categories. -/
theorem derivedAbelianLowerShriek_isTriangulated (h : s.AbelianLowerShriekAcyclic) :
    letI := s.derivedAbelianLowerShriekCommShift h
    s.derivedAbelianLowerShriek.IsTriangulated := by
  let := s.derivedAbelianLowerShriekCommShift h
  have _ : (s.derivedAbelianLowerShriekAdjunction h).CommShift ℤ :=
    (s.derivedAbelianLowerShriekAdjunction h).commShift_of_rightAdjoint ℤ
  exact (s.derivedAbelianLowerShriekAdjunction h).isTriangulated_leftAdjoint

/-- `Lπ_!(F[0])` is bounded above by `0`: the derived lower shriek of an abelian sheaf placed in
degree zero has no cohomology in positive degrees. -/
theorem isLE_derivedAbelianLowerShriek_obj_single (h : s.AbelianLowerShriekAcyclic)
    (X : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :
    (s.derivedAbelianLowerShriek.obj
      ((DerivedCategory.singleFunctor _ 0).obj X)).IsLE 0 := by
  refine isLE_of_forall_hom_eq_zero _ _ 0 1 (by ring) fun Y hY f ↦ ?_
  have hadj := s.derivedAbelianLowerShriekAdjunction h
  have _ : s.derivedAbelianLowerShriek.IsLeftAdjoint := hadj.isLeftAdjoint
  have _ : s.derivedAbelianLowerShriek.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hz : (hadj.homEquiv _ _) f = 0 :=
    DerivedCategory.TStructure.t.zero ((hadj.homEquiv _ _) f) 0 1 (by lia)
  rw [← (hadj.homEquiv _ _).symm_apply_apply f, hz, Adjunction.homEquiv_counit,
    Functor.map_zero, zero_comp]

section Triangulated

variable [s.derivedAbelianLowerShriek.CommShift ℤ] [s.derivedAbelianLowerShriek.IsTriangulated]

/-- The δ-functor structure on `F ↦ Lπ_!(F[0])`: the one on `F ↦ F[0]` composed with the exact
functor `Lπ_!`. -/
abbrev derivedLowerShriekDeltaFunctorStructure :
    (DerivedCategory.singleFunctor (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) 0 ⋙
        s.derivedAbelianLowerShriek).DeltaFunctorStructure
      (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
      (DerivedCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC})) :=
  (singleDeltaFunctorStructure
    (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})).comp s.derivedAbelianLowerShriek

/-- The distinguished triangle of `D(Ab(D))` that `Lπ_!` attaches to a short exact sequence of
abelian sheaves on the total category. -/
abbrev derivedLowerShriekTriangle
    {S : ShortComplex (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})}
    (hS : S.ShortExact) :
    Triangle (DerivedCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC})) :=
  Triangle.mk
    ((DerivedCategory.singleFunctor (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) 0 ⋙
      s.derivedAbelianLowerShriek).map S.f)
    ((DerivedCategory.singleFunctor (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) 0 ⋙
      s.derivedAbelianLowerShriek).map S.g)
    (s.derivedLowerShriekDeltaFunctorStructure.δ hS)

/-- The triangle attached to a short exact sequence by `Lπ_!` is distinguished. -/
theorem derivedLowerShriekTriangle_distinguished
    {S : ShortComplex (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})}
    (hS : S.ShortExact) :
    s.derivedLowerShriekTriangle hS ∈
      distTriang (DerivedCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC})) :=
  s.derivedLowerShriekDeltaFunctorStructure.distinguished hS

/-- The family `F ↦ H^{-n}(Lπ_! F)` as a homological δ-functor, given the exactness of `Lπ_!`
and the vanishing of `H^{> 0}(Lπ_!(F[0]))`. Its connecting morphisms are those of the long exact
homology sequence of the distinguished triangle of a short exact sequence. -/
def derivedLowerShriekHomologyDeltaFunctorOfIsLE
    (hLE : ∀ X : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC},
      (s.derivedAbelianLowerShriek.obj
        ((DerivedCategory.singleFunctor _ 0).obj X)).IsLE 0) :
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) where
  functor n := s.derivedAbelianLowerShriekHomology n
  additive _ := inferInstance
  δ {_} hS n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequenceδ
        (s.derivedLowerShriekTriangle hS) (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)
  map_g_δ {_} hS n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).comp_homologySequenceδ
        (s.derivedLowerShriekTriangle hS) (s.derivedLowerShriekTriangle_distinguished hS)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)
  δ_map_f {_} hS n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequenceδ_comp
        (s.derivedLowerShriekTriangle hS) (s.derivedLowerShriekTriangle_distinguished hS)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)
  epi_map_g {S} hS := by
    have _ := hLE S.X₁
    have hz : (DerivedCategory.homologyFunctor
        (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequenceδ
          (s.derivedLowerShriekTriangle hS) (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) rfl = 0 :=
      (DerivedCategory.isZero_of_isLE
        (s.derivedAbelianLowerShriek.obj
          ((DerivedCategory.singleFunctor _ 0).obj S.X₁)) 0 (-((0 : ℕ) : ℤ) + 1)
        (by norm_num)).eq_of_tgt _ _
    exact ((DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequence_epi_shift_map_mor₂_iff
        (s.derivedLowerShriekTriangle hS) (s.derivedLowerShriekTriangle_distinguished hS)
        (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) rfl).2 hz
  exact_map {_} hS n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequence_exact₂
        (s.derivedLowerShriekTriangle hS) (s.derivedLowerShriekTriangle_distinguished hS)
        (-(n : ℤ))
  exact_δ₁ {_} hS n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequence_exact₃
        (s.derivedLowerShriekTriangle hS) (s.derivedLowerShriekTriangle_distinguished hS)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)
  exact_δ₂ {_} hS n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequence_exact₁
        (s.derivedLowerShriekTriangle hS) (s.derivedLowerShriekTriangle_distinguished hS)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)
  δ_naturality {_ _} hS hT φ n :=
    (DerivedCategory.homologyFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).homologySequenceδ_naturality
        (deltaFunctorMapTriangleHom s.derivedLowerShriekDeltaFunctorStructure hS hT φ)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)

end Triangulated

/-- The family `F ↦ H^{-n}(Lπ_! F)` of `derivedAbelianLowerShriekHomology`, equipped with the
connecting morphisms of the long exact homology sequence of the distinguished triangle of a short
exact sequence, is a homological δ-functor from abelian sheaves on the total category to abelian
sheaves on the base. -/
def derivedLowerShriekHomologyDeltaFunctor (h : s.AbelianLowerShriekAcyclic) :
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) :=
  letI := s.derivedAbelianLowerShriekCommShift h
  haveI := s.derivedAbelianLowerShriek_isTriangulated h
  s.derivedLowerShriekHomologyDeltaFunctorOfIsLE
    (s.isLE_derivedAbelianLowerShriek_obj_single h)

/-- The degree-`n` functor of `derivedLowerShriekHomologyDeltaFunctor` is `H^{-n}(Lπ_! -)`. -/
theorem derivedLowerShriekHomologyDeltaFunctor_functor (h : s.AbelianLowerShriekAcyclic)
    (n : ℕ) :
    (s.derivedLowerShriekHomologyDeltaFunctor h).functor n =
      s.derivedAbelianLowerShriekHomology n :=
  rfl

/-- The acyclicity of the generators for `Lπ_!`: every direct sum of the free abelian sheaves
`j_{U!} ℤ_U` on objects of the total category is carried by `Lπ_!` to a complex with no
cohomology in negative degrees, i.e. `L_m π_!` vanishes on it for `m ≥ 1`. -/
abbrev AbelianLowerShriekGeneratorsAcyclic : Prop :=
  ∀ P : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC},
    Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC,
      vC, uC} s.topology P →
    (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj P)).IsGE 0

/-- When lower shriek is exact, `Lπ_!(F[0])` has no cohomology in negative degrees. -/
theorem isGE_derivedAbelianLowerShriek_obj_single_of_preservesFiniteLimits
    [PreservesFiniteLimits s.abelianLowerShriek]
    (P : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :
    (s.derivedAbelianLowerShriek.obj
      ((DerivedCategory.singleFunctor _ 0).obj P)).IsGE 0 := by
  have hinv : (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
      (ComplexShape.up ℤ)).IsInvertedBy
        (s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) := by
    intro X Y f hf
    have _ : IsIso (DerivedCategory.Qh.map f) :=
      Localization.inverts DerivedCategory.Qh _ f hf
    rw [← NatIso.isIso_map_iff s.abelianLowerShriek.mapDerivedCategoryFactorsh f]
    dsimp
    infer_instance
  have _ := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
      (ComplexShape.up ℤ))
    s.abelianLowerShriek.mapDerivedCategory s.abelianLowerShriek.mapDerivedCategoryFactorsh
  have e := Functor.leftDerivedUnique s.abelianLowerShriek.mapDerivedCategory
    s.derivedAbelianLowerShriek
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w uD vD uC,
      vC, uC, vD, uD} s.topology s.base.J s.p)
    s.abelianLowerShriek.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
      (ComplexShape.up ℤ))
  have e₂ : (DerivedCategory.singleFunctor
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) 0).obj
        (s.abelianLowerShriek.obj P) ≅
      s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj P) :=
    ((s.abelianLowerShriek.mapDerivedCategorySingleFunctor 0).app P).symm ≪≫
      (e.app ((DerivedCategory.singleFunctor _ 0).obj P)).symm
  exact DerivedCategory.TStructure.t.isGE_of_iso e₂ 0

/-- The acyclicity of the generators holds when lower shriek is exact. -/
theorem abelianLowerShriekGeneratorsAcyclic_of_preservesFiniteLimits
    [PreservesFiniteLimits s.abelianLowerShriek] :
    s.AbelianLowerShriekGeneratorsAcyclic :=
  fun P _ ↦ s.isGE_derivedAbelianLowerShriek_obj_single_of_preservesFiniteLimits P

/-- The δ-functor `derivedLowerShriekHomologyDeltaFunctor` is coeffaceable once the generators
are `Lπ_!`-acyclic. -/
theorem coeffaceable_derivedLowerShriekHomology (h : s.AbelianLowerShriekAcyclic)
    (hgen : s.AbelianLowerShriekGeneratorsAcyclic) :
    (s.derivedLowerShriekHomologyDeltaFunctor h).Coeffaceable := by
  refine Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero _
    fun X n ↦ ?_
  obtain ⟨P, hP, p, hp⟩ :=
    Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnitsAb.{max w uD vD uC,
      vC, uC} s.topology X
  have _ := hgen P hP
  exact ⟨P, p, hp, DerivedCategory.isZero_of_isGE
    (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj P)) 0
    (-((n + 1 : ℕ) : ℤ)) (by push_cast; lia)⟩

/-- Once the generators are `Lπ_!`-acyclic, the homological δ-functor `F ↦ H^{-n}(Lπ_! F)` is
universal: every morphism of δ-functors into it is determined by, and can be prescribed
arbitrarily in, degree zero. -/
theorem isUniversal_derivedLowerShriekHomology (h : s.AbelianLowerShriekAcyclic)
    (hgen : s.AbelianLowerShriekGeneratorsAcyclic) :
    (s.derivedLowerShriekHomologyDeltaFunctor h).IsUniversal :=
  have := s.coeffaceable_derivedLowerShriekHomology h hgen
  Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

end Derived

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
