module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece.SplittingIndependence

/-!
# The graded pieces of an exterior power: the Künneth retraction

The Künneth decomposition of `⋀ⁿT.X₂` along a splitting as a direct sum, the retraction onto a
summand, its descent to `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`, and the consequence that the comparison onto
the graded piece is an isomorphism as soon as the sequence splits.
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

section Splitting

variable {T : ShortComplex
    (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))}
  (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₁)
  (AG₃ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₃)
  (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₂)

/-! ### The Künneth decomposition as a direct sum, and the retraction onto a summand -/

/-- Sheaves of modules have finite biproducts: they form an abelian category, hence a preadditive
one with finite products. Supplied explicitly at these binders because Mathlib keeps
`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts` as a local instance of its own
abelian file. With `Stacks.Nat.finite_subtype_add_eq` this is what makes the Künneth coproduct,
indexed by the antidiagonal, a biproduct — and so gives it projections. -/
local instance hasFiniteBiproductsSheaves :
    HasFiniteBiproducts
      (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- **The Künneth decomposition of `⋀ⁿT.X₂` along a splitting**, as an isomorphism out of the
coproduct of the summands `⋀^pT.X₁ ⊗ ⋀^qT.X₃`. -/
noncomputable def exteriorPowerProdIsoOfSplitting (sp : T.Splitting) (n : ℕ) :
    (∐ exteriorPowerProdSummand AF₁ AG₃ n) ≅ A₂.exteriorPower n :=
  haveI := _root_.SheafOfModules.isIso_exteriorPowerProdHom AF₁ AG₃ A₂ T.f sp.r sp.s T.g
    sp.f_r sp.s_g T.zero sp.s_r sp.id n
  asIso (exteriorPowerProdHom AF₁ AG₃ A₂ T.f sp.s n)

/-- The forward map of the Künneth isomorphism `exteriorPowerProdIsoOfSplitting` is
`exteriorPowerProdHom` for the section of the splitting. -/
@[simp]
theorem exteriorPowerProdIsoOfSplitting_hom (sp : T.Splitting) (n : ℕ) :
    (exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp n).hom =
      exteriorPowerProdHom AF₁ AG₃ A₂ T.f sp.s n :=
  rfl

/-- **The retraction of `⋀ⁿT.X₂` onto the weight-`p` Künneth summand**: invert the Künneth
isomorphism, read the coproduct as a biproduct, and project. This is the `ρ_p` the injectivity of
`SheafOfModules.exteriorGradedQuotientComparison` is proved with. -/
noncomputable def exteriorKunnethRetraction (sp : T.Splitting) (p q n : ℕ) (h : p + q = n) :
    A₂.exteriorPower n ⟶
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Osharp)).obj (AF₁.exteriorPower p, AG₃.exteriorPower q) :=
  (exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp n).inv ≫
    (biproduct.isoCoproduct (exteriorPowerProdSummand AF₁ AG₃ n)).inv ≫
      biproduct.π (exteriorPowerProdSummand AF₁ AG₃ n) (ULift.up ⟨(p, q), h⟩)

/-- The coproduct injection of the weight-`(p, q)` summand, followed by the Künneth
isomorphism, is the wedge-product morphism of that bidegree. -/
theorem sigmaι_comp_exteriorPowerProdIsoOfSplitting (sp : T.Splitting) (p q n : ℕ)
    (h : p + q = n) :
    Sigma.ι (exteriorPowerProdSummand AF₁ AG₃ n) (ULift.up ⟨(p, q), h⟩) ≫
        (exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp n).hom =
      prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s p q n h :=
  Sigma.ι_desc _ _

/-- **The retraction is a retraction**: the weight-`(p, q)` summand, included into `⋀ⁿT.X₂` by
the wedge-product morphism and then projected back, is the identity. -/
theorem prodWedgeHomOfEq_comp_exteriorKunnethRetraction (sp : T.Splitting) (p q n : ℕ)
    (h : p + q = n) :
    prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s p q n h ≫
        exteriorKunnethRetraction AF₁ AG₃ A₂ sp p q n h =
      𝟙 ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Osharp)).obj (AF₁.exteriorPower p, AG₃.exteriorPower q)) := by
  rw [exteriorKunnethRetraction,
    ← sigmaι_comp_exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp p q n h, Category.assoc,
    Iso.hom_inv_id_assoc, biproduct.isoCoproduct_inv, ← Category.assoc, Sigma.ι_desc,
    biproduct.ι_π_self]
  rfl

/-- **The retraction kills every other Künneth summand.** -/
theorem prodWedgeHomOfEq_comp_exteriorKunnethRetraction_of_ne (sp : T.Splitting) (p q n : ℕ)
    (h : p + q = n) (p' q' : ℕ) (h' : p' + q' = n) (hne : (p', q') ≠ (p, q)) :
    prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s p' q' n h' ≫
        exteriorKunnethRetraction AF₁ AG₃ A₂ sp p q n h =
      0 := by
  have hidx : (ULift.up ⟨(p', q'), h'⟩ : ULift.{u} {pq : ℕ × ℕ // pq.1 + pq.2 = n}) ≠
      ULift.up ⟨(p, q), h⟩ := by
    intro hcon
    exact hne (congrArg Subtype.val (congrArg ULift.down hcon))
  rw [exteriorKunnethRetraction,
    ← sigmaι_comp_exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp p' q' n h', Category.assoc,
    Iso.hom_inv_id_assoc, biproduct.isoCoproduct_inv, ← Category.assoc, Sigma.ι_desc,
    biproduct.ι_π_ne (exteriorPowerProdSummand AF₁ AG₃ n) hidx]

/-- **The section of a splitting is a section of the surjection of the presentation of
[Stacks, Tag 01CJ]**, in degree `m + 1`: `⋀^{m+1}sp.s ≫ ⋀^{m+1}T.g = 𝟙`, because the exterior
power of a composite is the composite of the exterior powers and `sp.s ≫ T.g = 𝟙`. -/
theorem pieceMap_splitting_comp_pieceMap_g (sp : T.Splitting) (m : ℕ) :
    AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
          ((m + 1 : ℕ) : ℤ) ≫
        A₂.exterior_isExteriorAlgebra.pieceMap AG₃.exterior_isExteriorAlgebra T.g
          ((m + 1 : ℕ) : ℤ) =
      𝟙 (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)) := by
  rw [← GradedAlgebra.IsExteriorAlgebra.pieceMap_comp, sp.s_g,
    GradedAlgebra.IsExteriorAlgebra.pieceMap_id]

/-- `SheafOfModules.pieceMap_splitting_comp_pieceMap_g` with the second morphism read as the
surjection of the presentation of [Stacks, Tag 01CJ], which it is by definition. -/
theorem pieceMap_splitting_comp_relComplex_g (sp : T.Splitting) (m : ℕ) :
    AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
          ((m + 1 : ℕ) : ℤ) ≫
        (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g =
      𝟙 (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)) :=
  have hg : (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g =
      A₂.exterior_isExteriorAlgebra.pieceMap AG₃.exterior_isExteriorAlgebra T.g
        ((m + 1 : ℕ) : ℤ) := rfl
  Eq.trans
    (congrArg (fun z => AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
        ((m + 1 : ℕ) : ℤ) ≫ z) hg)
    (pieceMap_splitting_comp_pieceMap_g AG₃ A₂ sp m)

/-- **The splitting-free comparison is the Künneth comparison of any splitting.** Whenever the
short complex `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` splits,
`SheafOfModules.exteriorGradedQuotientComparison` is the wedge-product morphism along the
inclusion of the sub and the section of the quotient, projected onto the graded piece — read
through the transport between the two spellings of the total degree.

Together with `SheafOfModules.splittingToExteriorGraded_eq`, which says those wedge-product
morphisms do not depend on the splitting, this is the gluing of [Stacks, Section 0FMK] in exact
form: over every open on which the sequence splits the splitting-free comparison agrees with the
local Künneth comparison, and the local comparisons agree with each other. It is also the route
to the injectivity of the comparison:
`SheafOfModules.exteriorGradedQuotientComparison_eq_whiskerLeft_eqToHom_comp` reads it as an
equality with `SheafOfModules.splittingToExteriorGraded`, and
`SheafOfModules.mono_exteriorGradedQuotientComparison_of_splitting` then settles it. -/
theorem exteriorGradedQuotientComparison_eq_of_splitting (hS : T.Exact) (hepi : Epi T.g)
    (sp : T.Splitting) (k m : ℕ) :
    exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k)).map
          (AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
              ((m + 1 : ℕ) : ℤ) ≫
            eqToHom (exteriorPiece_one_add_eq A₂ m).symm) ≫
        toExteriorGraded AF₁ A₂ T.f k m :=
  Stacks.CategoryTheory.eq_map_comp_of_section
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower k))
    (AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
      ((m + 1 : ℕ) : ℤ))
    (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g
    (pieceMap_splitting_comp_relComplex_g AG₃ A₂ sp m)
    (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m)
    (eqToHom (exteriorPiece_one_add_eq A₂ m).symm) (toExteriorGraded AF₁ A₂ T.f k m)
    (tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m)

/-! ### The retraction kills the next step of the filtration -/

/-- **Transporting the degree of the map induced on exterior powers.** For `d = d'` the map
induced by `f` in degree `d`, followed by the transport to degree `d'`, is the transport followed
by the map induced in degree `d'`. This is what reconciles the two spellings `((m+1 : ℕ) : ℤ)`
and `((1 + m : ℕ) : ℤ)` of the complementary degree, the first being the one
[Stacks, Tag 01CJ] is stated at and the second the one the wedge filtration is. -/
theorem pieceMap_comp_eqToHom
    {M N : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    {B D : GradedAlgebra.{u, u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    {ιB : M ⟶ B.piece 1} {ιD : N ⟶ D.piece 1} (hB : GradedAlgebra.IsExteriorAlgebra B ιB)
    (hD : GradedAlgebra.IsExteriorAlgebra D ιD) (f : M ⟶ N) (d d' : ℤ) (hd : d = d') :
    hB.pieceMap hD f d ≫ eqToHom (congrArg D.piece hd) =
      eqToHom (congrArg B.piece hd) ≫ hB.pieceMap hD f d' := by
  subst hd
  simp

/-- Tensoring on the left with `⋀^rT.X₁` preserves a coproduct indexed by a type in the universe
of the space, which is what the Künneth coproduct `∐ SheafOfModules.exteriorPowerProdSummand` —
indexed by the lifted antidiagonal — is. The generic instance is instantiated by hand because at
the concrete site the search for it does not succeed in this import closure; the same is done in
`Stacks.SheafOfModules.TopWedge.preservesColimit_parallelPair_tensorLeftFunctor`. -/
local instance preservesColimit_discrete_tensorLeftFunctor (r : ℕ) {I : Type u}
    (Q : I → SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    PreservesColimit (Discrete.functor Q)
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower r)) := by
  have : Limits.PreservesColimitsOfSize.{u, u}
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower r)) :=
    Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight
      (Opens.grothendieckTopology ↥X) Osharp (AF₁.exteriorPower r)
  infer_instance

/-- **The retraction kills a Künneth summand of the next step of the filtration**, before the
degree arithmetic: the weight-`(a, b)` summand of `⋀^{a+b}T.X₂`, wedged with `⋀^{k+1}T.X₁` into
`⋀ⁿT.X₂` and then projected back onto the weight-`(k, 1+(a+b))` summand, is zero.

The associativity square at the second structural map `sp.s`
(`SheafOfModules.mulSheafTensorId_comp_prodWedgeHom`) identifies that composite with the
weight-`(k+1+a, b)` summand inclusion, projected; and `k + 1 + a ≠ k`, so
`SheafOfModules.prodWedgeHomOfEq_comp_exteriorKunnethRetraction_of_ne` kills it. -/
theorem whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_exteriorKunnethRetraction
    (sp : T.Splitting) (k a b : ℕ) (h : k + (1 + (a + b)) = k + 1 + (a + b)) :
    (AF₁.exteriorPower (k + 1) ◁ prodWedgeHom AF₁ AG₃ A₂ T.f sp.s a b) ≫
        prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) (a + b) ≫
          exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + (a + b)) (k + 1 + (a + b)) h = 0 := by
  have hab : k + 1 + a + b = k + 1 + (a + b) := by omega
  have hne : (k + 1 + a, b) ≠ (k, 1 + (a + b)) := fun hcon => by
    have h1 : k + 1 + a = k := congrArg Prod.fst hcon
    omega
  have hzero := prodWedgeHomOfEq_comp_exteriorKunnethRetraction_of_ne AF₁ AG₃ A₂ sp k
    (1 + (a + b)) (k + 1 + (a + b)) h (k + 1 + a) b hab hne
  refine Stacks.CategoryTheory.eq_zero_of_iso_comp_eq_zero
    (α_ (AF₁.exteriorPower (k + 1)) (AF₁.exteriorPower a) (AG₃.exteriorPower b)) _ ?_
  refine Eq.trans (Stacks.CategoryTheory.comp_comp_comp_eqToHom_comp_eqToHom_symm_comp
    (α_ (AF₁.exteriorPower (k + 1)) (AF₁.exteriorPower a) (AG₃.exteriorPower b)).hom
    (AF₁.exteriorPower (k + 1) ◁ prodWedgeHom AF₁ AG₃ A₂ T.f sp.s a b)
    (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) (a + b))
    (congrArg A₂.exterior.piece (add_assoc ((k + 1 : ℕ) : ℤ) (a : ℤ) (b : ℤ)).symm)
    (exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + (a + b)) (k + 1 + (a + b)) h)).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      eqToHom (congrArg A₂.exterior.piece
          (add_assoc ((k + 1 : ℕ) : ℤ) (a : ℤ) (b : ℤ)).symm).symm ≫
        exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + (a + b)) (k + 1 + (a + b)) h)
    (mulSheafTensorId_comp_prodWedgeHom AF₁ AG₃ A₂ T.f sp.s (k + 1) a b).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      Osharp)).map
      ((GradedAlgebra.mulSheaf AF₁.exterior ((k + 1 : ℕ) : ℤ) (a : ℤ),
          𝟙 (AG₃.exteriorPower b)) :
        (AF₁.exteriorPower (k + 1) ⊗ AF₁.exteriorPower a, AG₃.exteriorPower b) ⟶
          (AF₁.exteriorPower (k + 1 + a), AG₃.exteriorPower b)) ≫ z)
    ((Category.assoc _ _ _).symm.trans hzero)) ?_
  exact comp_zero

/-- `SheafOfModules.whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_exteriorKunnethRetraction`
with the total degree of the second factor named by a hypothesis, which is the shape the
coproduct decomposition of `⋀^mT.X₂` presents its summands in. -/
theorem whiskerLeft_prodWedgeHomOfEq_comp_prodWedgeHom_comp_exteriorKunnethRetraction
    (sp : T.Splitting) (k m a b : ℕ) (hab : a + b = m) (h : k + (1 + m) = k + 1 + m) :
    (AF₁.exteriorPower (k + 1) ◁ prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s a b m hab) ≫
        prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m ≫
          exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + m) (k + 1 + m) h = 0 := by
  subst hab
  rw [prodWedgeHomOfEq_rfl]
  exact whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_exteriorKunnethRetraction
    AF₁ AG₃ A₂ sp k a b h

/-- **(★): the retraction onto the weight-`k` Künneth summand kills the `(k+1)`-st step of the
wedge filtration.** The wedge-product morphism `⋀^{k+1}T.X₁ ⊗ ⋀^mT.X₂ ⟶ ⋀ⁿT.X₂`, whose image is
`F^{k+1}⋀ⁿT.X₂`, composed with `ρ_k`, is zero.

The second factor `⋀^mT.X₂` is decomposed by the Künneth isomorphism of the splitting, and
tensoring with `⋀^{k+1}T.X₁` preserves that coproduct because the tensor product of sheaves of
modules preserves all colimits in each variable ([Stacks, Tag 05NB]); on the `(a, b)` summand the
composite is
`SheafOfModules.whiskerLeft_prodWedgeHomOfEq_comp_prodWedgeHom_comp_exteriorKunnethRetraction`,
which is zero because every bidegree arising has first entry `k + 1 + a > k`.

This is what makes `ρ_k` descend to `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`
(`SheafOfModules.exteriorKunnethRetractionDescent`). -/
theorem prodWedgeHom_comp_exteriorKunnethRetraction (sp : T.Splitting) (k m : ℕ)
    (h : k + (1 + m) = k + 1 + m) :
    prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m ≫
        exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + m) (k + 1 + m) h =
      0 := by
  refine Stacks.CategoryTheory.eq_zero_of_iso_comp_eq_zero
    (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower (k + 1))).mapIso
      (exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp m)) _ ?_
  refine Limits.Cofan.IsColimit.hom_ext
    (Limits.isColimitOfHasCoproductOfPreservesColimit
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF₁.exteriorPower (k + 1)))
      (exteriorPowerProdSummand AF₁ AG₃ m)) _ 0 ?_
  intro i
  obtain ⟨⟨⟨a, b⟩, hab⟩⟩ := i
  refine Eq.trans ?_ comp_zero.symm
  have hmap : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
          (AF₁.exteriorPower (k + 1))).map
        (Limits.Sigma.ι (exteriorPowerProdSummand AF₁ AG₃ m) (ULift.up ⟨(a, b), hab⟩)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
          (AF₁.exteriorPower (k + 1))).map
        (exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp m).hom =
        AF₁.exteriorPower (k + 1) ◁ prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s a b m hab := by
    refine Eq.trans (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
      (AF₁.exteriorPower (k + 1))).map_comp _ _).symm ?_
    refine Eq.trans (congrArg ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
        (AF₁.exteriorPower (k + 1))).map
      (sigmaι_comp_exteriorPowerProdIsoOfSplitting AF₁ AG₃ A₂ sp a b m hab)) ?_
    rw [Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp
      (AF₁.exteriorPower (k + 1)) (prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s a b m hab),
      Stacks.CategoryTheory.map_id_app, Category.id_comp]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m ≫
        exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + m) (k + 1 + m) h) hmap) ?_
  exact whiskerLeft_prodWedgeHomOfEq_comp_prodWedgeHom_comp_exteriorKunnethRetraction
    AF₁ AG₃ A₂ sp k m a b hab h

/-! ### The retraction descends, and the comparison is an isomorphism -/

/-- **The retraction `ρ_k` descends to `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`**, by (★)
(`SheafOfModules.prodWedgeHom_comp_exteriorKunnethRetraction`): it kills the morphism whose
cokernel that quotient is. -/
noncomputable def exteriorKunnethRetractionDescent (sp : T.Splitting) (k m : ℕ)
    (h : k + (1 + m) = k + 1 + m) :
    cokernel (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) ⟶
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Osharp)).obj (AF₁.exteriorPower k, AG₃.exteriorPower (1 + m)) :=
  cokernel.desc (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m)
    (exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + m) (k + 1 + m) h)
    (prodWedgeHom_comp_exteriorKunnethRetraction AF₁ AG₃ A₂ sp k m h)

/-- The defining equation of `SheafOfModules.exteriorKunnethRetractionDescent`. -/
@[reassoc]
theorem cokernelπ_comp_exteriorKunnethRetractionDescent (sp : T.Splitting) (k m : ℕ)
    (h : k + (1 + m) = k + 1 + m) :
    cokernel.π (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m) ≫
        exteriorKunnethRetractionDescent AF₁ AG₃ A₂ sp k m h =
      exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + m) (k + 1 + m) h :=
  cokernel.π_desc _ _ _

/-- **The descended retraction is a retraction of the Künneth comparison onto the graded piece.**
Composing `SheafOfModules.splittingToExteriorGraded` with the inclusion of the graded piece into
`⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂` and then with the descended retraction gives the identity: the first two
make the weight-`k` summand inclusion, projected, and `ρ_k` retracts that summand
(`SheafOfModules.prodWedgeHomOfEq_comp_exteriorKunnethRetraction`). -/
theorem splittingToExteriorGraded_comp_arrow_comp_exteriorKunnethRetractionDescent
    (sp : T.Splitting) (k m : ℕ) (h : k + (1 + m) = k + 1 + m) :
    splittingToExteriorGraded AF₁ AG₃ A₂ sp k m ≫
        (imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow ≫
          exteriorKunnethRetractionDescent AF₁ AG₃ A₂ sp k m h =
      𝟙 ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Osharp)).obj (AF₁.exteriorPower k, AG₃.exteriorPower (1 + m))) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ exteriorKunnethRetractionDescent AF₁ AG₃ A₂ sp k m h)
    (splittingToExteriorGraded_comp_arrow AF₁ AG₃ A₂ sp k m)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => prodWedgeHom AF₁ AG₃ A₂ T.f sp.s k (1 + m) ≫ z)
    (Eq.trans (Category.assoc _ _ _)
      (congrArg (fun z => eqToHom (congrArg A₂.exterior.piece
            (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫ z)
        (cokernelπ_comp_exteriorKunnethRetractionDescent AF₁ AG₃ A₂ sp k m h)))) ?_
  exact (Category.assoc _ _ _).symm.trans
    (prodWedgeHomOfEq_comp_exteriorKunnethRetraction AF₁ AG₃ A₂ sp k (1 + m) (k + 1 + m) h)

/-- **The Künneth comparison onto the graded piece is a monomorphism.** It is a split
monomorphism: `SheafOfModules.exteriorKunnethRetractionDescent`, after the inclusion of the
graded piece, retracts it. Together with (★) this is the injectivity half of
[Stacks, Section 0FMK] for a split sequence. -/
theorem mono_splittingToExteriorGraded (sp : T.Splitting) (k m : ℕ) :
    Mono (splittingToExteriorGraded AF₁ AG₃ A₂ sp k m) :=
  Stacks.CategoryTheory.mono_of_comp_eq_id _
    ((imageSubobject (exteriorGradedHom AF₁ A₂ T.f k m)).arrow ≫
      exteriorKunnethRetractionDescent AF₁ AG₃ A₂ sp k m (by omega))
    (splittingToExteriorGraded_comp_arrow_comp_exteriorKunnethRetractionDescent
      AF₁ AG₃ A₂ sp k m (by omega))

/-- The two spellings `m + 1` and `1 + m` of the complementary degree, as an equality of integer
degrees; [Stacks, Tag 01CJ] is stated at the first and the wedge filtration at the second. -/
theorem exteriorDegree_succ_eq (m : ℕ) : ((m + 1 : ℕ) : ℤ) = ((1 + m : ℕ) : ℤ) := by
  omega

/-- **The splitting-free comparison is the Künneth comparison of any splitting, up to the
transport of the complementary degree.** This is
`SheafOfModules.exteriorGradedQuotientComparison_eq_of_splitting` with the right-hand side read
as `SheafOfModules.splittingToExteriorGraded`: the two differ only in whether the complementary
degree is spelled `m + 1`, as [Stacks, Tag 01CJ] has it, or `1 + m`, as the wedge filtration has
it, and `SheafOfModules.pieceMap_comp_eqToHom` moves the transport between them past the map
induced on exterior powers. -/
theorem exteriorGradedQuotientComparison_eq_whiskerLeft_eqToHom_comp (hS : T.Exact)
    (hepi : Epi T.g) (sp : T.Splitting) (k m : ℕ) :
    exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m =
      (AF₁.exteriorPower k ◁
          eqToHom (congrArg AG₃.exterior.piece (exteriorDegree_succ_eq m))) ≫
        splittingToExteriorGraded AF₁ AG₃ A₂ sp k m := by
  refine Eq.trans (exteriorGradedQuotientComparison_eq_of_splitting AF₁ AG₃ A₂ hS hepi sp k m) ?_
  have hbr : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
          (AF₁.exteriorPower k)).map
        (AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
            ((m + 1 : ℕ) : ℤ) ≫
          eqToHom (exteriorPiece_one_add_eq A₂ m).symm) =
      AF₁.exteriorPower k ◁
        (AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
            ((m + 1 : ℕ) : ℤ) ≫
          eqToHom (exteriorPiece_one_add_eq A₂ m).symm) := by
    rw [Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp
      (AF₁.exteriorPower k)
      (AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
          ((m + 1 : ℕ) : ℤ) ≫
        eqToHom (exteriorPiece_one_add_eq A₂ m).symm),
      Stacks.CategoryTheory.map_id_app, Category.id_comp]
  refine Eq.trans (congrArg (fun z => z ≫ toExteriorGraded AF₁ A₂ T.f k m) hbr) ?_
  refine Eq.trans (congrArg (fun z => (AF₁.exteriorPower k ◁ z) ≫
      toExteriorGraded AF₁ A₂ T.f k m)
    (pieceMap_comp_eqToHom AG₃.exterior_isExteriorAlgebra A₂.exterior_isExteriorAlgebra sp.s
      ((m + 1 : ℕ) : ℤ) ((1 + m : ℕ) : ℤ) (exteriorDegree_succ_eq m))) ?_
  refine Eq.trans (congrArg (fun z => z ≫ toExteriorGraded AF₁ A₂ T.f k m)
    (MonoidalCategory.whiskerLeft_comp (AF₁.exteriorPower k)
      (eqToHom (congrArg AG₃.exterior.piece (exteriorDegree_succ_eq m)))
      (AG₃.exterior_isExteriorAlgebra.pieceMap A₂.exterior_isExteriorAlgebra sp.s
        ((1 + m : ℕ) : ℤ)))) ?_
  exact Category.assoc _ _ _

/-- **The splitting-free comparison onto the graded piece is a monomorphism when the sequence
splits.** By `SheafOfModules.exteriorGradedQuotientComparison_eq_whiskerLeft_eqToHom_comp` it is
a transport of the complementary degree, whiskered with `⋀^kT.X₁`, followed by the Künneth
comparison of the splitting, and that comparison is a split monomorphism
(`SheafOfModules.mono_splittingToExteriorGraded`). -/
theorem mono_exteriorGradedQuotientComparison_of_splitting (hS : T.Exact) (hepi : Epi T.g)
    (sp : T.Splitting) (k m : ℕ) :
    Mono (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
  Eq.mpr
    (congrArg Mono
      (exteriorGradedQuotientComparison_eq_whiskerLeft_eqToHom_comp AF₁ AG₃ A₂ hS hepi sp k m))
    (Stacks.CategoryTheory.mono_comp_of_mono _ _
      (Stacks.CategoryTheory.mono_whiskerLeft_eqToHom (AF₁.exteriorPower k)
        (congrArg AG₃.exterior.piece (exteriorDegree_succ_eq m)))
      (mono_splittingToExteriorGraded AF₁ AG₃ A₂ sp k m))

/-- **The quotient-level comparison is a monomorphism when the sequence splits.** It is
`SheafOfModules.exteriorGradedQuotientComparison` followed by the inclusion of the graded piece
into `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`, the comparison is a monomorphism once the sequence splits
(`SheafOfModules.mono_exteriorGradedQuotientComparison_of_splitting`) and the inclusion is one
because it is the arrow of a subobject.

This is the direction `SheafOfModules.mono_exteriorGradedQuotientComparison_of_mono_quotientHom`
does not give. That lemma takes monomorphy of this morphism to monomorphy of the comparison,
which is what the globalization of [Stacks, Section 0FMK] needs at the *end*; the localization
needs the converse, because what the splitting is available for is the comparison and what has to
cross restriction to an open is the quotient-level form. Costs 23,136 heartbeats against the
default budget of 200,000, the composite being matched against the definition of
`SheafOfModules.exteriorGradedQuotientHom` by a single defeq check. -/
theorem mono_exteriorGradedQuotientHom_of_splitting (hS : T.Exact) (hepi : Epi T.g)
    (sp : T.Splitting) (k m : ℕ) :
    Mono (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m) :=
  Stacks.CategoryTheory.mono_comp_of_mono _ _
    (mono_exteriorGradedQuotientComparison_of_splitting AF₁ AG₃ A₂ hS hepi sp k m)
    (Subobject.arrow_mono _)

/-- **The comparison of [Stacks, Section 0FMK] is an isomorphism when the sequence splits**:

`⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₃ ≅ gr^k⋀ⁿT.X₂`,  `n = k + 1 + m`.

It is an epimorphism with no hypothesis beyond short exactness
(`SheafOfModules.epi_exteriorGradedQuotientComparison`) and a monomorphism once the sequence
splits (`SheafOfModules.mono_exteriorGradedQuotientComparison_of_splitting`), and sheaves of
modules form a balanced category
(`Stacks.SheafOfModules.TopWedge.balanced_sheafOfModules`).

The splitting enters only through the monomorphy. It is not an extra hypothesis on the
*statement* of Section 0FMK: monomorphy is a local condition and the transitivity sequence of a
smooth morphism splits locally, so the general case follows from this one together with the
compatibility of `SheafOfModules.exteriorGradedQuotientComparison` with restriction to an open,
which is carried out in
`StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras`:
`SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split` is this statement with
the splitting asked for only over the members of an open covering. -/
theorem isIso_exteriorGradedQuotientComparison_of_splitting (hS : T.Exact) (hepi : Epi T.g)
    (sp : T.Splitting) (k m : ℕ) :
    IsIso (exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m) :=
  have := Stacks.SheafOfModules.TopWedge.balanced_sheafOfModules (X := X) (Osharp := Osharp)
  have := mono_exteriorGradedQuotientComparison_of_splitting AF₁ AG₃ A₂ hS hepi sp k m
  have := epi_exteriorGradedQuotientComparison AF₁ AG₃ A₂ hS hepi k m
  isIso_of_mono_of_epi _

end Splitting

end SheafOfModules

end
