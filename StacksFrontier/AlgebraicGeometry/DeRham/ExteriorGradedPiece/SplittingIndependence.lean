module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.Construction

/-!
# The graded pieces of an exterior power: independence of the splitting

For a short complex `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` of sheaves of modules: the Künneth comparison
`⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₃ ⟶ gr^k⋀ⁿT.X₂` attached to a splitting does not depend on the
splitting, and for a short exact sequence it is the splitting-free comparison out of the
exterior power of the quotient, onto the graded piece and read into the quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance] SheafOfModules.monoidalSheaves
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace SheafOfModules

open MonoidalCategory

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-! ### Independence of the splitting -/

section Splitting

variable {T : ShortComplex
    (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))}
  (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₁)
  (AG₃ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₃)
  (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₂)

/-- **The Künneth comparison `⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₃ ⟶ gr^k⋀ⁿT.X₂` attached to a splitting** of a
short complex `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0`, for the total degree `n = k + 1 + m`: the
wedge-product morphism along the inclusion of the sub and the section of the quotient, followed
by the projection onto the graded piece.

`SheafOfModules.splittingToExteriorGraded_eq` proves that it does not depend on the splitting. -/
def splittingToExteriorGraded (sp : T.Splitting) (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        Osharp)).obj (AF₁.exteriorPower k, AG₃.exteriorPower (1 + m)) ⟶
      exteriorGraded AF₁ A₂ T.f k m :=
  (AF₁.exteriorPower k ◁
      AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
        ((1 + m : ℕ) : ℤ)) ≫
    toExteriorGraded AF₁ A₂ T.f k m

/-- **The exterior power of the transition automorphism acts trivially on the graded piece.**
Composing the wedge-product morphism `⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₂ ⟶ ⋀ⁿT.X₂` with `⋀ⁿθ` and then
projecting to `⋀ⁿT.X₂/F^{k+1}` gives the same as projecting directly: this is
`SheafOfModules.prodWedgeHom_comp_pieceMap_transition_sub_id_comp_cokernelπ`, with the
difference of the two legs read as an equality. -/
theorem prodWedgeHom_comp_pieceMap_transition_comp_exteriorGradedHom (sp sp' : T.Splitting)
    (k m : ℕ) :
    prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) k (1 + m) ≫
        A₂.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra
            (sp.transition sp') ((k + (1 + m) : ℕ) : ℤ) ≫
          eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
            cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) =
      prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) k (1 + m) ≫
        eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) := by
  have h := prodWedgeHom_comp_pieceMap_transition_sub_id_comp_cokernelπ sp sp' AF₁ A₂ k m
  rw [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, sub_eq_zero] at h
  exact h

/-- The Künneth comparison of a splitting onto the graded piece, composed with the inclusion of
the graded piece into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`: it is the wedge-product morphism along the
inclusion of the sub and the section of the quotient, projected. -/
theorem splittingToExteriorGraded_comp_arrow (sp : T.Splitting) (k m : ℕ) :
    splittingToExteriorGraded AF₁ AG₃ A₂ sp k m ≫
        (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow =
      prodWedgeHom AF₁ AG₃ A₂ T.f sp.s k (1 + m) ≫
        eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) := by
  rw [splittingToExteriorGraded, Category.assoc, toExteriorGraded_comp_arrow]
  exact whiskerLeft_pieceMap_comp_exteriorGradedHom AF₁ AG₃ A₂ T.f sp.s k m

/-- **The Künneth comparison into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` does not depend on the splitting.**
The two sections differ by the unipotent transition automorphism `θ` of `T.X₂`
(`CategoryTheory.ShortComplex.Splitting.s_comp_transition`), which fixes the inclusion of the sub
(`CategoryTheory.ShortComplex.Splitting.f_comp_transition`); the two wedge-product morphisms
therefore differ by postcomposition with `⋀ⁿθ`
(`SheafOfModules.prodWedgeHom_comp_pieceMap`), and `⋀ⁿθ` is the identity on the `k`-th step of
the wedge filtration of `⋀ⁿT.X₂` modulo the `(k+1)`-st
(`SheafOfModules.prodWedgeHom_comp_pieceMap_transition_sub_id_comp_cokernelπ`). -/
theorem prodWedgeHom_splitting_comp_pieceMap_transition_comp_cokernelπ (sp sp' : T.Splitting)
    (k m : ℕ) :
    prodWedgeHom AF₁ AG₃ A₂ T.f sp.s k (1 + m) ≫
        A₂.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra
            (sp.transition sp') ((k + (1 + m) : ℕ) : ℤ) ≫
          eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
            cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) =
      prodWedgeHom AF₁ AG₃ A₂ T.f sp.s k (1 + m) ≫
        eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) := by
  rw [prodWedgeHom_eq_whiskerLeft_pieceMap_comp AF₁ AG₃ A₂ T.f sp.s k (1 + m)]
  simp only [Category.assoc]
  rw [prodWedgeHom_comp_pieceMap_transition_comp_exteriorGradedHom AF₁ A₂ sp sp' k m]

/-- **The Künneth comparison into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` does not depend on the splitting.** -/
theorem prodWedgeHom_splitting_comp_cokernelπ_eq (sp sp' : T.Splitting) (k m : ℕ) :
    prodWedgeHom AF₁ AG₃ A₂ T.f sp'.s k (1 + m) ≫
        eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) =
      prodWedgeHom AF₁ AG₃ A₂ T.f sp.s k (1 + m) ≫
        eqToHom (congrArg A₂.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) := by
  have hcomp0 := prodWedgeHom_comp_pieceMap AF₁ AG₃ A₂ A₂ T.f sp.s (sp.transition sp') k (1 + m)
  rw [sp.f_comp_transition sp', sp.s_comp_transition sp'] at hcomp0
  have hcomp : prodWedgeHom AF₁ AG₃ A₂ T.f sp'.s k (1 + m) =
      prodWedgeHom AF₁ AG₃ A₂ T.f sp.s k (1 + m) ≫
        A₂.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra
          (sp.transition sp') ((k + (1 + m) : ℕ) : ℤ) := hcomp0
  rw [hcomp, Category.assoc]
  exact prodWedgeHom_splitting_comp_pieceMap_transition_comp_cokernelπ AF₁ AG₃ A₂ sp sp' k m

/-- **The Künneth comparison onto the graded piece does not depend on the splitting.** For two
splittings `sp`, `sp'` of a short complex `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` the two comparisons
`⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₃ ⟶ gr^k⋀ⁿT.X₂` agree. This is
`SheafOfModules.prodWedgeHom_splitting_comp_cokernelπ_eq` read inside the graded piece, the
inclusion of the graded piece into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` being a monomorphism.

This is the agreement of the local Künneth decompositions that [Stacks, Section 0FMK] uses to
glue them. -/
theorem splittingToExteriorGraded_eq (sp sp' : T.Splitting) (k m : ℕ) :
    splittingToExteriorGraded AF₁ AG₃ A₂ sp' k m =
      splittingToExteriorGraded AF₁ AG₃ A₂ sp k m := by
  refine (cancel_mono (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow).1 ?_
  refine Eq.trans (splittingToExteriorGraded_comp_arrow AF₁ AG₃ A₂ sp' k m) ?_
  exact Eq.trans (prodWedgeHom_splitting_comp_cokernelπ_eq AF₁ AG₃ A₂ sp sp' k m)
    (splittingToExteriorGraded_comp_arrow AF₁ AG₃ A₂ sp k m).symm

/-! ### The comparison out of the exterior power of the quotient -/

/-- The two spellings `1 + m` and `m + 1` of the total degree, as an equality of exterior
powers. They are equal but not definitionally equal, and [Stacks, Tag 01CJ] is stated at the
second while the wedge filtration is stated at the first, so the transport is named once here. -/
theorem exteriorPiece_one_add_eq
    {Z : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (B : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) Z) (m : ℕ) :
    B.exterior.piece ((1 : ℤ) + (m : ℤ)) = B.exterior.piece (((m + 1 : ℕ) : ℤ)) :=
  congrArg B.exterior.piece (by push_cast; ring)

/-- **The first morphism of the presentation of [Stacks, Tag 01CJ], as a wedge morphism.** The
three-term complex `T.X₁ ⊗ ⋀^mT.X₂ ⟶ ⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃` of that tag has as its first
morphism the wedge-product morphism `⋀^1T.X₁ ⊗ ⋀^mT.X₂ ⟶ ⋀^{1+m}T.X₂`, precomposed with the
degree-one generator of the exterior algebra of `T.X₁` and followed by the transport of the total
degree. -/
theorem relComplex_f_eq (m : ℕ) :
    (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).f =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((AF₁.exteriorGenerator, 𝟙 (A₂.exteriorPower m)) :
            (T.X₁, A₂.exteriorPower m) ⟶ (AF₁.exteriorPower 1, A₂.exteriorPower m)) ≫
        prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) 1 m ≫
          eqToHom (exteriorPiece_one_add_eq A₂ m) := by
  change GradedAlgebra.generatorMul (T.f ≫ A₂.exteriorGenerator) (m : ℤ) ≫
    eqToHom (exteriorPiece_one_add_eq A₂ m) = _
  rw [generatorMul_eq_generatorTensorId_comp_prodWedgeHom AF₁ A₂ T.f m, Category.assoc]

/-- **The canonical morphism onto `gr^k` kills the first morphism of the presentation of
[Stacks, Tag 01CJ], tensored with `⋀^kT.X₁`.** By `SheafOfModules.relComplex_f_eq` that morphism
factors through the wedge morphism `⋀^1T.X₁ ⊗ ⋀^mT.X₂ ⟶ ⋀^{1+m}T.X₂`, which the canonical
morphism kills
(`SheafOfModules.tensorLeftFunctor_map_prodWedgeHom_comp_toExteriorGraded`); the transport of the
total degree cancels against its inverse. -/
theorem tensorLeftFunctor_map_relComplex_f_comp_toExteriorGraded (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
            (eqToHom (exteriorPiece_one_add_eq A₂ m).symm) ≫
          toExteriorGraded AF₁ A₂ T.f k m =
      0 :=
  by
  rw [relComplex_f_eq AF₁ AG₃ A₂ m]
  exact tensorLeftFunctor_map_generatorTensorId_comp_toExteriorGraded AF₁ A₂ T.f k m
    (exteriorPiece_one_add_eq A₂ m)

/-- **The canonical splitting-free comparison in the shape [Stacks, Section 0FMK] states it**:

`⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₃ ⟶ gr^k⋀ⁿT.X₂`,  `n = k + 1 + m`,

for a short exact sequence `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` of sheaves of modules. No splitting
enters.

It is the descent of `SheafOfModules.toExteriorGraded` along the presentation
`T.X₁ ⊗ ⋀^mT.X₂ ⟶ ⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃ ⟶ 0` of [Stacks, Tag 01CJ] tensored with
`⋀^kT.X₁`, which is still a presentation because the tensor product of sheaves of modules is
right exact (`Stacks.SheafOfModules.TopWedge.relCokernelIsColimit`); the canonical morphism onto
the graded piece kills the relation by
`SheafOfModules.tensorLeftFunctor_map_relComplex_f_comp_toExteriorGraded`.

`SheafOfModules.splittingToExteriorGraded_eq` says the local Künneth comparisons all agree, and
`SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientComparison` is the
equation that pins this morphism down. -/
noncomputable def exteriorGradedQuotientComparison (hS : T.Exact) (hepi : Epi T.g) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).obj
        (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)) ⟶
      exteriorGraded AF₁ A₂ T.f k m :=
  haveI := hepi
  (Stacks.SheafOfModules.TopWedge.relCokernelIsColimit AF₁ A₂ AG₃ T.f T.g T.zero hS k m).desc
    (CokernelCofork.ofπ
      (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (eqToHom (exteriorPiece_one_add_eq A₂ m).symm) ≫
        toExteriorGraded AF₁ A₂ T.f k m)
      (tensorLeftFunctor_map_relComplex_f_comp_toExteriorGraded AF₁ AG₃ A₂ k m))

/-- **The defining equation of the splitting-free comparison of
`SheafOfModules.exteriorGradedQuotientComparison`**: precomposed with `⋀^kT.X₁` tensored with the
surjection `⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃`, it is the canonical morphism onto the graded piece, read
through the transport of the total degree. That surjection stays an epimorphism after tensoring,
so this equation determines the comparison. -/
theorem tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientComparison (hS : T.Exact)
    (hepi : Epi T.g) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g ≫
        exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (eqToHom (exteriorPiece_one_add_eq A₂ m).symm) ≫
        toExteriorGraded AF₁ A₂ T.f k m :=
  have := hepi
  Cofork.IsColimit.π_desc
    (Stacks.SheafOfModules.TopWedge.relCokernelIsColimit AF₁ A₂ AG₃ T.f T.g T.zero hS k m)

/-- **The splitting-free comparison onto the graded piece is an epimorphism.** Its defining
equation exhibits it, after precomposition with the surjection of the presentation of
[Stacks, Tag 01CJ] tensored with `⋀^kT.X₁`, as a transport followed by the canonical epimorphism
`⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₂ ↠ gr^k⋀ⁿT.X₂`; a morphism whose composite on the left is an epimorphism is
one.

This is one half of the statement that the comparison is an isomorphism, which
[Stacks, Section 0FMK] asserts; the other half is
`SheafOfModules.mono_exteriorGradedQuotientComparison_of_splitting`, which needs a splitting. -/
theorem epi_exteriorGradedQuotientComparison (hS : T.Exact) (hepi : Epi T.g) (k m : ℕ) :
    Epi (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
  Stacks.CategoryTheory.epi_of_comp_eq_epi_comp
    (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
      (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g)
    (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m)
    (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
      (eqToHom (exteriorPiece_one_add_eq A₂ m).symm))
    (toExteriorGraded AF₁ A₂ T.f k m)
    (tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m)
    (Stacks.CategoryTheory.epi_map_eqToHom _ _) (epi_toExteriorGraded AF₁ A₂ T.f k m)

/-! ### The comparison read into the quotient, where the image subobject does not appear -/

/-- **The splitting-free comparison read into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`** instead of into the graded
piece: `SheafOfModules.exteriorGradedQuotientComparison` followed by the inclusion of the graded
piece.

It is the descent of `SheafOfModules.exteriorGradedHom` along the presentation of
[Stacks, Tag 01CJ] tensored with `⋀^kT.X₁`
(`SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom`), and the
comparison is a monomorphism as soon as it is
(`SheafOfModules.mono_exteriorGradedQuotientComparison_of_mono_quotientHom`).

**Its target carries no image subobject**, which is what makes it the morphism the localization
of [Stacks, Section 0FMK] should be carried out at: one functor fewer has to be crossed than for
the comparison itself, and the two definitionally-equal `Abelian` instances at the concrete
objects of the wedge filtration — the pitfall recorded in the implementation notes — never have to
meet an image lemma. -/
noncomputable def exteriorGradedQuotientHom (hS : T.Exact) (hepi : Epi T.g) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).obj
        (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)) ⟶
      cokernel (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) :=
  exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m ≫
    (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow

/-- **The defining equation of the quotient-level comparison**: precomposed with `⋀^kT.X₁`
tensored with the surjection `⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃` of [Stacks, Tag 01CJ] it is
`SheafOfModules.exteriorGradedHom`, read through the transport of the total degree. That
surjection stays an epimorphism after tensoring, so this equation determines the morphism — which
is how a restriction of it is to be identified. -/
theorem tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom (hS : T.Exact)
    (hepi : Epi T.g) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g ≫
        exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (eqToHom (exteriorPiece_one_add_eq A₂ m).symm) ≫
        exteriorGradedHom AF₁ A₂ T.f k m :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun z => z ≫ (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow)
        (tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi
          k m))
      (Eq.trans (Category.assoc _ _ _)
        (congrArg
          (fun z => ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
                (AF₁.exteriorPower k)).map
              (eqToHom (exteriorPiece_one_add_eq A₂ m).symm) ≫ z)
          (toExteriorGraded_comp_arrow AF₁ A₂ T.f k m))))

/-- **The comparison onto the graded piece is a monomorphism as soon as the quotient-level
comparison is.** The inclusion of the graded piece is what the two differ by, and a morphism
whose composite with anything is a monomorphism is one. -/
theorem mono_exteriorGradedQuotientComparison_of_mono_quotientHom (hS : T.Exact) (hepi : Epi T.g)
    (k m : ℕ) (h : Mono (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m)) :
    Mono (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
  have : Mono (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m ≫
      (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow) := h
  mono_of_mono (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m)
    (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow

end Splitting

end SheafOfModules

end
