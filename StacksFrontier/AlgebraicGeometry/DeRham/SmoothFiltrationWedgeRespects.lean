module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltrationWedgeAction
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceCut

/-!
# Wedge multiplication by a pulled-back form respects the filtration of Section 50.12

Let `f : X ⟶ Y` be a morphism of schemes over `S`, `U ⊆ Y` open and `ω` a `p`-form on `U`. Left
multiplication by the pull back `ρ(f⁻¹ω)` of `ω` is a cochain of degree `p` on the restriction of
`Ω^•_{X/S}` to `f⁻¹(U)`
(`SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain`). This file proves that it
carries the `k`-th step of the filtration of Section 50.12 into the `(k + p)`-th, which is the
hypothesis `CochainComplex.Filtered.RespectsFiltration` of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CochainAction` for the Katz–Oda
description of the Gauss–Manin connection in [Stacks, Tag 0FMN].

## Main definitions

* `Stacks.DeRhamSmooth.pulledBackOpen` and `Stacks.DeRhamSmooth.pulledBackForm`: the open `f⁻¹(U)`
  and the section `ρ(f⁻¹ω)` of `Ω^p_{X/S}` over it.

## Main results

* `Stacks.DeRhamSmooth.respectsFiltration_restrictedLeftMulCochain`: **left multiplication by
  `ρ(f⁻¹ω)` respects the filtration.**
* `Stacks.DeRhamSmooth.d_pulledBackForm`: `d ρ(f⁻¹ω) = ρ(f⁻¹dω)`.
* `Stacks.DeRhamSmooth.respectsFiltration_δ_restrictedLeftMulCochain`: **so does its
  coboundary**, which is left multiplication by `ρ(f⁻¹dω)`.

## Implementation notes

The degree-`n` term of `F^k` is the image of the wedge map
`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{n-k}_{X/S} ⟶ Ω^n_{X/S}` (`Stacks.DeRhamSmooth.mk_ι_app_f_eq`), so it
suffices to check the claim on that wedge map. There it is checked on local sections: the
sections of the tensor product are locally sums of pure tensors (the sheafification unit is
locally surjective), and on a pure tensor `x ⊗ y` multiplication by `ρ(f⁻¹ω) = ex(a)` gives the
wedge map applied to `(a ∧ x) ⊗ y`, by associativity of the exterior algebra and multiplicativity
of `⋀(f^*Ω_{Y/S}) ⟶ ⋀Ω_{X/S}` (`Stacks.DeRhamSmooth.restrictedLeftMulCochain_stepWedge`). Every
crossing between the spellings of the categories of sheaves of modules involved is done by a term
applied with `exact`, never by rewriting. No `@[stacks]` attribute is attached here.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.DeRhamSmooth

section Generic

/-- **A morphism through which `E` factors by an epimorphism is killed by `Φ` followed by `ψ`
as soon as `E` is**, `Φ` preserving epimorphisms. -/
theorem map_comp_eq_zero_of_epi_fac {C₀ D₀ : Type*} [Category C₀] [Preadditive C₀]
    [Category D₀] [Preadditive D₀] (Φ : C₀ ⥤ D₀) [Φ.PreservesEpimorphisms] {A₀ B₀ T₀ : C₀}
    {Z₀ : D₀} (e : T₀ ⟶ A₀) [Epi e] (j : A₀ ⟶ B₀) (E : T₀ ⟶ B₀) (he : e ≫ j = E)
    (ψ : Φ.obj B₀ ⟶ Z₀) (hE : Φ.map E ≫ ψ = 0) : Φ.map j ≫ ψ = 0 := by
  refine (cancel_epi (Φ.map e)).mp ?_
  rw [comp_zero, ← Category.assoc, ← Φ.map_comp, he, hE]

/-- A morphism factoring through `j₀` is killed by `Φ` followed by `ψ` as soon as `j₀` is. -/
theorem map_comp_eq_zero_of_fac {C₀ D₀ : Type*} [Category C₀] [Preadditive C₀]
    [Category D₀] [Preadditive D₀] (Φ : C₀ ⥤ D₀) {A₀ A₁ B₀ : C₀} {Z₀ : D₀} (a : A₀ ⟶ A₁)
    (j₀ : A₁ ⟶ B₀) (j : A₀ ⟶ B₀) (hj : j = a ≫ j₀) (ψ : Φ.obj B₀ ⟶ Z₀)
    (h0 : Φ.map j₀ ≫ ψ = 0) : Φ.map j ≫ ψ = 0 := by
  rw [hj, Φ.map_comp, Category.assoc, h0, comp_zero]

end Generic

section WedgeAssoc

open _root_.SheafOfModules in
/-- **Left multiplication by the image of a section `a` of `⋀^pF`, on the image of a pure tensor
under the wedge map `⋀^kF ⊗ ⋀^qH ⟶ ⋀^{k+q}H`, is the wedge map applied to `(a ∧ x) ⊗ y`**: the
exterior algebra of `H` is associative and `⋀F ⟶ ⋀H` is multiplicative. -/
theorem mul_prodWedgeHom_unit_heq {Xt : TopCat.{u}}
    {Osharp : Sheaf (Opens.grothendieckTopology ↥Xt) CommRingCat.{u}}
    {F H : _root_.SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥Xt) Osharp)}
    (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥Xt) F)
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥Xt) H)
    (iF : F ⟶ H) (p k q : ℕ) (W : (Opens Xt)ᵒᵖ) (a : (AF.exteriorPower p).val.obj W)
    (x : (AF.exteriorPower k).val.obj W) (y : (A.exteriorPower q).val.obj W) :
    (A.exterior.mul (p : ℤ) ((k + q : ℕ) : ℤ)).app W
        (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
          (p : ℤ)).val.app W a)
        ((prodWedgeHom AF A A iF (𝟙 H) k q).val.app W
          ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower k) (A.exteriorPower q)).app W
            (x ⊗ₜ y))) ≍
      (prodWedgeHom AF A A iF (𝟙 H) (p + k) q).val.app W
        ((PresheafOfModules.tensorSheafUnit (AF.exteriorPower (p + k)) (A.exteriorPower q)).app W
          ((AF.exterior.mul (p : ℤ) (k : ℤ)).app W a x ⊗ₜ y)) := by
  have h1 := prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF k q W x y
  have h2 := prodWedgeHomIdRight_val_app_tensorSheafUnit AF A iF (p + k) q W
    ((AF.exterior.mul (p : ℤ) (k : ℤ)).app W a x) y
  have h3 := (AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).map_mul
    (p : ℤ) (k : ℤ) W a x
  refine (heq_of_eq (congrArg (fun z => (A.exterior.mul (p : ℤ) ((k + q : ℕ) : ℤ)).app W
    (((AF.exterior_isExteriorAlgebra.map A.exterior_isExteriorAlgebra iF).app
      (p : ℤ)).val.app W a) z) h1)).trans ?_
  refine (A.exterior.mul_assoc (p : ℤ) (k : ℤ) (q : ℤ) W _ _ y).symm.trans ?_
  refine heq_of_eq (Eq.trans (congrArg (fun z => (A.exterior.mul ((p : ℤ) + (k : ℤ)) (q : ℤ)).app
    W z y) h3.symm) h2.symm)

end WedgeAssoc

section Restricted

variable {Xr : RingedSpace.{u, u}} (V : Opens Xr)

/-- An open of `X` contained in `V` is the image of an open of the subspace `V`. -/
theorem exists_openOfRestrict_eq {Y₀ : Opens Xr} (hY : Y₀ ≤ V) :
    ∃ W : Opens ((Opens.toTopCat (Xr : TopCat)).obj V), openOfRestrict V W = Y₀ :=
  ⟨(Opens.map (Opens.inclusion' V)).obj Y₀, by
    rw [openOfRestrict, Opens.functor_map_eq_inf, inf_eq_left]
    exact hY⟩

/-- **A morphism between restrictions to `V` is zero as soon as it kills a locally surjective
family of sections.** If `η : R ⟶ N` is a locally surjective morphism of presheaves of abelian
groups on `X` and `ψ : N|_V ⟶ C|_V` kills `η(r)` for every section `r` of `R` over every open
inside `V`, then `ψ = 0`: every section of `N` is locally of the form `η(r)`, and `C` is
separated. -/
theorem restricted_hom_eq_zero_of_isLocallySurjective
    {N C : _root_.SheafOfModules.{u} (structureSheafRing Xr)}
    (ψ : (moduleRestriction Xr V).obj N ⟶ (moduleRestriction Xr V).obj C)
    {R : (Opens Xr)ᵒᵖ ⥤ AddCommGrpCat.{u}} (η : R ⟶ N.val.presheaf)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Xr) η]
    (hη : ∀ (W : Opens ((Opens.toTopCat (Xr : TopCat)).obj V))
      (r : R.obj (op (openOfRestrict V W))),
      ψ.val.app (op W) (η.app (op (openOfRestrict V W)) r) = 0) : ψ = 0 := by
  ext W t
  obtain ⟨W⟩ := W
  refine (Presheaf.IsSheaf.isSeparated C.isSheaf) (openOfRestrict V W)
    (Presheaf.imageSieve η t) (Presheaf.imageSieve_mem _ η t) _ _ ?_
  intro Y i ⟨r, hr⟩
  have hY : Y ≤ V := (leOfHom i).trans (openOfRestrict_le V W)
  obtain ⟨Y₀, rfl⟩ := exists_openOfRestrict_eq V hY
  have hle : Y₀ ≤ W := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := leOfHom i ⟨z, hz, rfl⟩
    exact (Subtype.ext hwz : w = z) ▸ hw
  have hnat := PresheafOfModules.naturality_apply ψ.val (homOfLE hle).op t
  refine hnat.symm.trans ?_
  have hi : i = V.isOpenEmbedding.functor.map (homOfLE hle) := Subsingleton.elim _ _
  subst hi
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans (congrArg (ψ.val.app (op Y₀)) hr.symm) (hη Y₀ r)

end Restricted

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (U : Y.Opens)

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-- The relative de Rham complex `Ω^•_{X/S}` as a sheaf of differential graded algebras. -/
abbrev deRhamDGA :=
  AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))

/-- **The wedge map `⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^q_{X/S} ⟶ Ω^m_{X/S}`**, for `k + q = m`, whose
image is the degree-`m` step at `k` of the filtration of `Ω^m_{X/S}` by the forms pulled back
from `Y`. -/
abbrev stepProdWedge (k q m : ℕ) (h : k + q = m) :=
  _root_.SheafOfModules.prodWedgeHomOfEq
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
    (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k q m h

/-- **The identification of the degree-`m` term of the `k`-th step of the filtration with the
step at `k` of the filtration of `Ω^m_{X/S}`**, read over `(f∘g)^{-1}𝒪_S`. -/
def stepXIsoExteriorStep (k m : ℕ) (hk : k ≤ m) :
    ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X (m : ℤ) ≅
      (deRhamSmoothRestrictScalars f g).obj
        (Subobject.underlying.obj (Scheme.Hom.relativeDifferentialsExteriorFiltration f g m k)) :=
  (Subobject.underlyingIso
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f (m : ℤ))).symm ≪≫
    Subobject.isoOfEq _ _ (mk_ι_app_f_eq f g k m hk) ≪≫
    Subobject.mapObjIso (deRhamSmoothExtendXIso f g m).inv _ ≪≫
    Stacks.GradedPieceImage.mapSubobjectsObjIso (deRhamSmoothRestrictScalars f g) _

/-- **The factorization of the wedge map through the degree-`m` term of the `k`-th step**: the
epimorphism onto the image of `stepProdWedge`, read over `(f∘g)^{-1}𝒪_S` and carried into the
step by `stepXIsoExteriorStep`. -/
def stepWedgeFactor (k q m : ℕ) (h : k + q = m) :=
  (deRhamSmoothRestrictScalars f g).map
      (@factorThruImageSubobject _ _ _ _ (stepProdWedge f g k q m h) _ ≫
        (Subobject.isoOfEq _ _
          (_root_.SheafOfModules.exteriorImageFiltration_eq_imageSubobject _ _ _ k q m h)).inv) ≫
    (stepXIsoExteriorStep f g k m (by omega)).inv

/-- **The wedge map onto the degree-`m` term of `Ω^•_{X/S}`**, read over `(f∘g)^{-1}𝒪_S`. -/
abbrev stepWedge (k q m : ℕ) (h : k + q = m) :=
  (deRhamSmoothRestrictScalars f g).map (stepProdWedge f g k q m h) ≫
    (deRhamSmoothExtendXIso f g m).inv

/-- An image factorization, read through a change of description of the image and a functor. -/
theorem map_factorThru_isoOfEq_inv_comp_map_arrow {C₁ : Type*} [Category* C₁] {D₁ : Type*}
    [Category* D₁] (U' : C₁ ⥤ D₁) {Z A : C₁} (R : Subobject Z) (w : A ⟶ Z) {hi : HasImage w}
    (h : R = imageSubobject w) :
    U'.map (factorThruImageSubobject w ≫ (Subobject.isoOfEq R (imageSubobject w) h).inv) ≫
      U'.map R.arrow = U'.map w :=
  Eq.trans (U'.map_comp _ _).symm
    (congrArg U'.map (Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun u => _ ≫ u) (Subobject.ofLE_arrow h.ge))
        (imageSubobject_arrow_comp w))))

/-- **`stepWedgeFactor` factors the wedge map through the step of the filtration.** -/
theorem stepWedgeFactor_comp_stepι (k q m : ℕ) (h : k + q = m) :
    stepWedgeFactor f g k q m h ≫ (deRhamSmoothFiltration f g).stepι (k : ℤ) (m : ℤ) =
      stepWedge f g k q m h := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ u) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ _ ≫ u)
    (Subobject.underlyingIso_hom_comp_eq_mk
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f (m : ℤ)))) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ u) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ _ ≫ u) (Subobject.ofLE_arrow _)) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ u) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ _ ≫ u)
    (Subobject.mapObjIso_inv_arrow (deRhamSmoothExtendXIso f g m).inv _)) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ u)
    (mapSubobjectsObjIso_inv_exteriorPowerRestriction_arrow_assoc f g m _
      (deRhamSmoothExtendXIso f g m).inv)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun u => u ≫ (deRhamSmoothExtendXIso f g m).inv)
    (map_factorThru_isoOfEq_inv_comp_map_arrow (deRhamSmoothRestrictScalars f g) _
      (stepProdWedge f g k q m h) _)

/-- `stepWedgeFactor` is an epimorphism: it is the restriction of scalars of an epimorphism onto
an image, followed by isomorphisms. -/
theorem epi_stepWedgeFactor (k q m : ℕ) (h : k + q = m) :
    Epi (stepWedgeFactor f g k q m h) := by
  have h0 : Epi (@factorThruImageSubobject _ _ _ _ (stepProdWedge f g k q m h) _) :=
    Limits.instEpiFactorThruImageSubobjectOfHasEqualizers _
  exact @epi_comp _ _ _ _ _ _
    (@Functor.map_epi _ _ _ _ (deRhamSmoothRestrictScalars f g) inferInstance _ _ _
      (@epi_comp _ _ _ _ _ _ h0 _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))))
    _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))

/-- The open `f⁻¹(U)` of the ringed space `(X, (f ∘ g)^{-1}𝒪_S)`. It is `f ⁻¹ᵁ U` by `rfl`; it is
named so that instance search sees an open of `inverseImageBase (f ≫ g)` rather than of the
scheme `X`. -/
def pulledBackOpen : Opens (inverseImageBase (f ≫ g)).carrier := f ⁻¹ᵁ U

/-- **The pull back `ρ(f⁻¹ω)` of a `p`-form `ω` on `U ⊆ Y`**, as a section of `Ω^p_{X/S}` over
`f⁻¹(U)`, in the `ℤ`-graded complex of the differential graded algebra. -/
def pulledBackForm (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) :
    ((deRhamDGA f g).complex.X (p : ℤ)).val.obj (op (pulledBackOpen f g U)) :=
  ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f p = (p : ℤ))).inv.val.app (op (f ⁻¹ᵁ U))
    (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f p).val.app
      ((opensMap (relativeBase f g)).op.obj (op U))
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω))

/-- The cochain of left multiplication by `ρ(f⁻¹ω)` on a local section, by definition. -/
theorem cochain_v_app_eq (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U))
    (n m : ℤ) (h : n + (p : ℤ) = m) (W : Opens ((Opens.toTopCat (X : TopCat)).obj
      (pulledBackOpen f g U)))
    (x : ((deRhamDGA f g).complex.X n).val.obj (op (openOfRestrict (pulledBackOpen f g U) W))) :
    ((SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U)
        (deRhamDGA f g) (pulledBackForm f g U p ω)).v n m h).val.app (op W) x =
      ((deRhamDGA f g).complex.XIsoOfEq (show (p : ℤ) + n = m by omega)).hom.val.app
        (op (openOfRestrict (pulledBackOpen f g U) W))
        (((deRhamDGA f g).mul (p : ℤ) n).app (op (openOfRestrict (pulledBackOpen f g U) W))
          (((deRhamDGA f g).complex.X (p : ℤ)).val.map
            (homOfLE (openOfRestrict_le (pulledBackOpen f g U) W)).op
            (pulledBackForm f g U p ω)) x) := rfl

/-- A transport of sheaves of modules does not move local sections, up to `HEq`. -/
theorem eqToHom_val_app_heq_of_eq {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}} {M M' : _root_.SheafOfModules.{u} R₀} (hM : M = M')
    (W : C₀ᵒᵖ) (x : M.val.obj W) : (eqToHom hM).val.app W x ≍ x := by
  subst hM
  rfl

/-- The identification of a term of an extension by zero with the original term does not move
local sections, up to `HEq`. -/
theorem extendXIso_inv_val_app_heq {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}} (K : CochainComplex (_root_.SheafOfModules.{u} R₀) ℕ) {i : ℕ}
    {i' : ℤ} (h : ComplexShape.embeddingUpNat.f i = i') (W : C₀ᵒᵖ) (x : (K.X i).val.obj W) :
    (K.extendXIso ComplexShape.embeddingUpNat h).inv.val.app W x ≍ x := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.inv]
  exact eqToHom_val_app_heq_of_eq _ _ _

/-- A transport between two equal degrees of a complex does not move local sections, up to
`HEq`. -/
theorem XIsoOfEq_hom_val_app_heq {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}} (K : CochainComplex (_root_.SheafOfModules.{u} R₀) ℤ) {i j : ℤ}
    (h : i = j) (W : C₀ᵒᵖ) (x : (K.X i).val.obj W) :
    (K.XIsoOfEq h).hom.val.app W x ≍ x := by
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom]
  exact eqToHom_val_app_heq_of_eq _ _ _

/-- The graded multiplication is congruent in its second degree, up to `HEq`. -/
theorem gradedMul_heq_right {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
    {R₀ : Sheaf J₀ RingCat.{u}} (Bg : _root_.SheafOfModules.GradedAlgebra.{u, u} R₀)
    (i : ℤ) {j j' : ℤ} (hj : j = j') (W : C₀ᵒᵖ) (a : (Bg.piece i).val.obj W)
    (b : (Bg.piece j).val.obj W) (b' : (Bg.piece j').val.obj W) (hb : b ≍ b') :
    (Bg.mul i j).app W a b ≍ (Bg.mul i j').app W a b' := by
  subst hj
  cases hb
  rfl

/-- **The pull back `ρ(f⁻¹ω)` restricted to an open of `f⁻¹(U)` is the image of a section of
`⋀^p(f^*Ω_{Y/S})`.** -/
theorem pulledBackForm_res_heq (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U))
    (W : Opens ((Opens.toTopCat (X : TopCat)).obj (pulledBackOpen f g U))) :
    ((deRhamDGA f g).complex.X (p : ℤ)).val.map
        (homOfLE (openOfRestrict_le (pulledBackOpen f g U) W)).op (pulledBackForm f g U p ω) ≍
      ((((pulledBackDifferentialsAlgebras f g).exterior_isExteriorAlgebra.map
          (Scheme.Hom.deRhamAlgebras (f ≫ g)).exterior_isExteriorAlgebra
          (Scheme.Hom.relativeDifferentialsShortComplex f g).f).app (p : ℤ)).val.app
        (op (openOfRestrict (pulledBackOpen f g U) W))
        (((pulledBackDifferentialsAlgebras f g).exteriorPower p).val.map
          (homOfLE (openOfRestrict_le (pulledBackOpen f g U) W)).op
          ((pulledBackFormsComparison f g p).val.app ((opensMap (relativeBase f g)).op.obj (op U))
            (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
              ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω)))) := by
  have hρ := congrArg (fun φ => φ.val.app ((opensMap (relativeBase f g)).op.obj (op U))
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω))
    (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g p)
  have h1 := PresheafOfModules.naturality_apply (deRhamSmoothExtendXIso f g p).inv.val
    (homOfLE (openOfRestrict_le (pulledBackOpen f g U) W)).op
    (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f p).val.app
      ((opensMap (relativeBase f g)).op.obj (op U))
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω))
  have h2 := PresheafOfModules.naturality_apply
    (((pulledBackDifferentialsAlgebras f g).exterior_isExteriorAlgebra.map
          (Scheme.Hom.deRhamAlgebras (f ≫ g)).exterior_isExteriorAlgebra
          (Scheme.Hom.relativeDifferentialsShortComplex f g).f).app (p : ℤ)).val
    (homOfLE (openOfRestrict_le (pulledBackOpen f g U) W)).op
    ((pulledBackFormsComparison f g p).val.app ((opensMap (relativeBase f g)).op.obj (op U))
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω))
  refine (heq_of_eq h1.symm).trans ?_
  refine (extendXIso_inv_val_app_heq _ _ _ _).trans ?_
  refine heq_of_eq ?_
  refine Eq.trans (congrArg _ hρ) ?_
  exact h2.symm

/-- The section `a = c_p(f⁻¹ω)` of `⋀^p(f^*Ω_{Y/S})` over `f⁻¹(U)` whose image is `ρ(f⁻¹ω)`. -/
abbrev pulledBackExteriorSection (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) :
    ((pulledBackDifferentialsAlgebras f g).exteriorPower p).val.obj (op (pulledBackOpen f g U)) :=
  (pulledBackFormsComparison f g p).val.app ((opensMap (relativeBase f g)).op.obj (op U))
    (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
      ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω)

/-- **Left multiplication by `ρ(f⁻¹ω)` on the image of a pure tensor.** On the image under the
wedge map of `x ⊗ y`, with `x` a section of `⋀^k(f^*Ω_{Y/S})` and `y` of `Ω^q_{X/S}`, left
multiplication by `ρ(f⁻¹ω)` is the wedge map applied to `(a ∧ x) ⊗ y`, where `a` is the section of
`⋀^p(f^*Ω_{Y/S})` whose image is `ρ(f⁻¹ω)`. -/
theorem restrictedLeftMulCochain_stepWedge (p k q n : ℕ) (hn : k + q = n)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U))
    (W : Opens ((Opens.toTopCat (X : TopCat)).obj (pulledBackOpen f g U)))
    (x : ((pulledBackDifferentialsAlgebras f g).exteriorPower k).val.obj
      (op (openOfRestrict (pulledBackOpen f g U) W)))
    (y : ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q).val.obj
      (op (openOfRestrict (pulledBackOpen f g U) W))) :
    ((SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U)
        (deRhamDGA f g) (pulledBackForm f g U p ω)).v (n : ℤ) ((p + n : ℕ) : ℤ)
          (by push_cast; ring)).val.app (op W)
      ((stepWedge f g k q n hn).val.app (op (openOfRestrict (pulledBackOpen f g U) W))
        ((PresheafOfModules.tensorSheafUnit
          ((pulledBackDifferentialsAlgebras f g).exteriorPower k)
          ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q)).app
            (op (openOfRestrict (pulledBackOpen f g U) W)) (x ⊗ₜ y))) =
    (stepWedge f g (p + k) q (p + n) (by omega)).val.app
        (op (openOfRestrict (pulledBackOpen f g U) W))
      ((PresheafOfModules.tensorSheafUnit
          ((pulledBackDifferentialsAlgebras f g).exteriorPower (p + k))
          ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q)).app
            (op (openOfRestrict (pulledBackOpen f g U) W))
        (((pulledBackDifferentialsAlgebras f g).exterior.mul (p : ℤ) (k : ℤ)).app
            (op (openOfRestrict (pulledBackOpen f g U) W))
          (((pulledBackDifferentialsAlgebras f g).exteriorPower p).val.map
            (homOfLE (openOfRestrict_le (pulledBackOpen f g U) W)).op
            (pulledBackExteriorSection f g U p ω)) x ⊗ₜ y)) := by
  refine eq_of_heq ?_
  refine (heq_of_eq (cochain_v_app_eq f g U p ω _ _ _ W _)).trans ?_
  refine (XIsoOfEq_hom_val_app_heq _ _ _ _).trans ?_
  have hz : (stepWedge f g k q n hn).val.app (op (openOfRestrict (pulledBackOpen f g U) W))
        ((PresheafOfModules.tensorSheafUnit
          ((pulledBackDifferentialsAlgebras f g).exteriorPower k)
          ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q)).app
            (op (openOfRestrict (pulledBackOpen f g U) W)) (x ⊗ₜ y)) ≍
      (stepProdWedge f g k q n hn).val.app (op (openOfRestrict (pulledBackOpen f g U) W))
        ((PresheafOfModules.tensorSheafUnit
          ((pulledBackDifferentialsAlgebras f g).exteriorPower k)
          ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q)).app
            (op (openOfRestrict (pulledBackOpen f g U) W)) (x ⊗ₜ y)) :=
    extendXIso_inv_val_app_heq _ _ _ _
  refine (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_mul
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
    p n (op (openOfRestrict (pulledBackOpen f g U) W)) _ _ _ _
    (pulledBackForm_res_heq f g U p ω W) hz).trans ?_
  refine (gradedMul_heq_right _ (p : ℤ) (show (n : ℤ) = ((k + q : ℕ) : ℤ) by rw [hn]) _ _ _ _
    (eqToHom_val_app_heq_of_eq _ _ _)).trans ?_
  refine (mul_prodWedgeHom_unit_heq _ _ _ p k q _ _ x y).trans ?_
  exact ((extendXIso_inv_val_app_heq _ _ _ _).trans
    (eqToHom_val_app_heq_of_eq (C₀ := Opens X)
      (congrArg (fun m : ℕ => (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂).exteriorPower m)
        (show p + k + q = p + n by omega)) _ _)).symm

/-- The wedge map at `k` followed by the projection onto the cokernel of a lower step of the
filtration vanishes, on every local section. -/
theorem cokernelπ_stepWedge_apply (k q m : ℕ) (h : k + q = m) (k' : ℤ) (hk' : k' ≤ (k : ℤ))
    (W : (Opens X)ᵒᵖ)
    (t : ((deRhamSmoothRestrictScalars f g).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        ((pulledBackDifferentialsAlgebras f g).exteriorPower k)).obj
        ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q))).val.obj W) :
    (cokernel.π ((deRhamSmoothFiltration f g).stepι k' (m : ℤ))).val.app W
      ((stepWedge f g k q m h).val.app W t) = 0 := by
  have hs := congrArg (fun φ => φ.f (m : ℤ))
    ((deRhamSmoothFiltration f g).filtration.step_comp_ι_app (homOfLE hk').op)
  have hE := congrArg (fun φ => φ.val.app W t) (stepWedgeFactor_comp_stepι f g k q m h)
  have hS := congrArg (fun φ => φ.val.app W ((stepWedgeFactor f g k q m h).val.app W t)) hs
  have hC := congrArg (fun φ => φ.val.app W
      (((deRhamSmoothFiltration f g).filtration.step (homOfLE hk').op).f (m : ℤ) |>.val.app W
        ((stepWedgeFactor f g k q m h).val.app W t)))
    (cokernel.condition ((deRhamSmoothFiltration f g).stepι k' (m : ℤ)))
  refine Eq.trans (congrArg _ hE.symm) ?_
  refine Eq.trans (congrArg _ hS.symm) ?_
  exact hC

/-- **Left multiplication by `ρ(f⁻¹ω)` carries the degree-`n` term of `F^k` into `F^{k'}`, for
`k' ≤ p + k`**, at `0 ≤ k ≤ n`. -/
theorem stepι_comp_restrictedLeftMulCochain_comp_cokernelπ (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k q n : ℕ) (hn : k + q = n)
    (k' : ℤ) (hk' : k' ≤ ((p + k : ℕ) : ℤ)) :
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
        ((deRhamSmoothFiltration f g).stepι (k : ℤ) (n : ℤ)) ≫
      ((SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U)
        (deRhamDGA f g) (pulledBackForm f g U p ω)).v (n : ℤ) ((p + n : ℕ) : ℤ)
          (by push_cast; ring)) ≫
      (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).map
        (cokernel.π ((deRhamSmoothFiltration f g).stepι k' ((p + n : ℕ) : ℤ))) = 0 := by
  have := epi_stepWedgeFactor f g k q n hn
  have hL : (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).IsLeftAdjoint :=
    moduleRestriction_isLeftAdjoint _ _
  refine @map_comp_eq_zero_of_epi_fac _ _ _ _ _ _
    (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
    (@Functor.preservesEpimorphisms_of_isLeftAdjoint _ _ _ _ _ hL) _ _ _ _
    (stepWedgeFactor f g k q n hn) this _ _
    (stepWedgeFactor_comp_stepι f g k q n hn) _ ?_
  refine @restricted_hom_eq_zero_of_isLocallySurjective _ (pulledBackOpen f g U) _ _ _ _
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (PresheafOfModules.tensorObj
        ((pulledBackDifferentialsAlgebras f g).exteriorPower k).val
        ((Scheme.Hom.deRhamAlgebras (f ≫ g)).exteriorPower q).val).presheaf)
    (Presheaf.isLocallySurjective_toSheafify' (Opens.grothendieckTopology X) _) ?_
  intro W r
  induction r using TensorProduct.inductionOn with
  | add a b ha hb => exact (congrArg _ (map_add _ a b)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) ha hb).trans (add_zero 0)))
  | tmul x y =>
    have hcore := restrictedLeftMulCochain_stepWedge f g U p k q n hn ω W x y
    exact (congrArg (fun z => (cokernel.π ((deRhamSmoothFiltration f g).stepι k'
      ((p + n : ℕ) : ℤ))).val.app _ z) hcore).trans
      (cokernelπ_stepWedge_apply f g (p + k) q (p + n) (by omega) k' hk' _ _)

/-- **Wedge multiplication by the pull back of a form respects the filtration of Section 50.12.**
For `f : X ⟶ Y` over `S`, an open `U ⊆ Y` and a `p`-form `ω` on `U`, left multiplication by
`ρ(f⁻¹ω)` on `Ω^•_{X/S}|_{f⁻¹(U)}` carries `F^k` into `F^{k+p}` for every `k`, in the sense of
`CochainComplex.Filtered.RespectsFiltration`. This is the input of the Katz–Oda description of
the Gauss–Manin connection, [Stacks, Tag 0FMN]. -/
theorem respectsFiltration_restrictedLeftMulCochain (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) :
    CochainComplex.Filtered.RespectsFiltration
      (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
      (deRhamSmoothFiltration f g : CochainComplex.Filtered
        (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))))
      (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U)
        (deRhamDGA f g) (pulledBackForm f g U p ω)) := by
  intro k k' hk n m h
  by_cases hn0 : n < 0
  · have hZ : IsZero ((moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).obj
        ((deRhamSmoothFiltration f g).X.X n)) :=
      Functor.map_isZero _ (HomologicalComplex.isZero_extend_X _ _ n fun i hi => by
        change (i : ℤ) = n at hi
        omega)
    rw [hZ.eq_of_src (_ ≫ _) 0, comp_zero]
  obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = n' := ⟨n.toNat, by omega⟩
  obtain rfl : m = ((p + n' : ℕ) : ℤ) := by omega
  by_cases hk0 : k ≤ 0
  · have h0 : IsIso ((deRhamSmoothFiltration f g).filtration.ι.app (op ((0 : ℕ) : ℤ))) :=
      AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos _ _ _ _ _ le_rfl
    have hk : IsIso ((deRhamSmoothFiltration f g).filtration.ι.app (op k)) :=
      AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos _ _ _ _ _ hk0
    have h0' : IsIso ((deRhamSmoothFiltration f g).stepι ((0 : ℕ) : ℤ) (n' : ℤ)) :=
      inferInstanceAs (IsIso ((HomologicalComplex.eval _ (ComplexShape.up ℤ) (n' : ℤ)).map
        ((deRhamSmoothFiltration f g).filtration.ι.app (op ((0 : ℕ) : ℤ)))))
    have hfac : (deRhamSmoothFiltration f g).stepι k (n' : ℤ) =
        ((deRhamSmoothFiltration f g).stepι k (n' : ℤ) ≫
          inv ((deRhamSmoothFiltration f g).stepι ((0 : ℕ) : ℤ) (n' : ℤ))) ≫
          (deRhamSmoothFiltration f g).stepι ((0 : ℕ) : ℤ) (n' : ℤ) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact map_comp_eq_zero_of_fac _ _ _ _ hfac _
      (stepι_comp_restrictedLeftMulCochain_comp_cokernelπ f g U p ω 0 n' n' (by omega) k'
        (by omega))
  obtain ⟨k₀, rfl⟩ : ∃ k₀ : ℕ, k = k₀ := ⟨k.toNat, by omega⟩
  by_cases hkn : k₀ ≤ n'
  · exact stepι_comp_restrictedLeftMulCochain_comp_cokernelπ f g U p ω k₀ (n' - k₀) n'
      (by omega) k' (by omega)
  · have hZ : IsZero ((moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U)).obj
        (((deRhamSmoothFiltration f g).filtration.obj (op (k₀ : ℤ))).X (n' : ℤ))) :=
      Functor.map_isZero _ (AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltered_filtration_obj_X
        _ _ _ _ _ (by omega) _ (by omega))
    rw [hZ.eq_of_src (_ ≫ _ ≫ _) 0]

/-- The pull back of a morphism of sheaves of modules carries the pull back of a local section to
the pull back of its image: naturality of the unit of `f⁻¹ ⊣ f_*`, on a local section. -/
theorem pullback_map_unit_apply {Ar Br : RingedSpace.{u}} (h : Ar ⟶ Br) {M N : Modules Br}
    (φ : M ⟶ N) (V : Opens Br) (x : M.val.obj (op V)) :
    ((_root_.pullback h).map φ).val.app (op ((Opens.map h.hom.base).obj V))
        (((_root_.pullbackPushforwardAdjunction h).unit.app M).val.app (op V) x) =
      ((_root_.pullbackPushforwardAdjunction h).unit.app N).val.app (op V) (φ.val.app (op V) x) :=
  (congrArg (fun ψ => ψ.val.app (op V) x)
    ((_root_.pullbackPushforwardAdjunction h).unit.naturality φ)).symm

/-- **The pull back of forms commutes with the de Rham differentials**: `d ρ(f⁻¹ω) = ρ(f⁻¹dω)`.
`ρ` is a morphism of complexes, the unit of `f⁻¹ ⊣ f_*` is natural, and the extension by zero
carries the differential of `Ω^•_{X/S}` to itself. -/
theorem d_pulledBackForm (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) :
    ((deRhamDGA f g).complex.d (p : ℤ) ((p : ℤ) + 1)).val.app (op (pulledBackOpen f g U))
        (pulledBackForm f g U p ω) =
      pulledBackForm f g U (p + 1)
        (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) := by
  have hD : (deRhamSmoothExtendXIso f g p).inv ≫
        (deRhamDGA f g).complex.d (p : ℤ) ((p : ℤ) + 1) =
      (AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (f ≫ g)))).d p (p + 1) ≫
        (deRhamSmoothExtendXIso f g (p + 1)).inv := by
    rw [show (deRhamDGA f g).complex.d (p : ℤ) ((p : ℤ) + 1) = _ from
      HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat (i := p) (j := p + 1) rfl rfl]
    exact Iso.inv_hom_id_assoc (deRhamSmoothExtendXIso f g p) _
  have hρ := (Stacks.DeRhamPullback.deRhamPullbackChain f g).comm p (p + 1)
  have eA := congrArg (fun φ => φ.val.app (op (pulledBackOpen f g U))
    (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f p).val.app
      ((opensMap (relativeBase f g)).op.obj (op U))
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω))) hD
  have eB := congrArg (fun φ => φ.val.app ((opensMap (relativeBase f g)).op.obj (op U))
    (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω)) hρ
  have eC := pullback_map_unit_apply (relativeBase f g) ((Scheme.Hom.deRhamComplex g).d p (p + 1))
    U ω
  have eC' : ((pulledBackDeRhamComplex f g).d p (p + 1)).val.app
        ((opensMap (relativeBase f g)).op.obj (op U))
        (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
          ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω) =
      ((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
          ((Scheme.Hom.deRhamComplex g).X (p + 1))).val.app (op U)
        (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) := eC
  have eB' : (((AlgebraicGeometry.SheafOfModules.deRhamComplex
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (f ≫ g)))).d p (p + 1)).val.app
        ((opensMap (relativeBase f g)).op.obj (op U))
        (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f p).val.app
          ((opensMap (relativeBase f g)).op.obj (op U))
          (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω))) =
      ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (p + 1)).val.app
        ((opensMap (relativeBase f g)).op.obj (op U))
        (((pulledBackDeRhamComplex f g).d p (p + 1)).val.app
          ((opensMap (relativeBase f g)).op.obj (op U))
          (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω)) := eB
  have eBC := eB'.trans (congrArg
    (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (p + 1)).val.app
      ((opensMap (relativeBase f g)).op.obj (op U))) eC')
  have eF := congrArg ((deRhamSmoothExtendXIso f g (p + 1)).inv.val.app
    (op (pulledBackOpen f g U))) eBC
  have key : ((deRhamSmoothExtendXIso f g p).inv ≫
        (deRhamDGA f g).complex.d (p : ℤ) ((p : ℤ) + 1)).val.app (op (pulledBackOpen f g U))
        (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f p).val.app
          ((opensMap (relativeBase f g)).op.obj (op U))
          (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X p)).val.app (op U) ω)) =
      (deRhamSmoothExtendXIso f g (p + 1)).inv.val.app (op (pulledBackOpen f g U))
        (((Stacks.DeRhamPullback.deRhamPullbackChain f g).f (p + 1)).val.app
          ((opensMap (relativeBase f g)).op.obj (op U))
          (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
            ((Scheme.Hom.deRhamComplex g).X (p + 1))).val.app (op U)
            (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω))) :=
    eA.trans eF
  exact key

/-- **The coboundary of wedge multiplication by the pull back of a form respects the filtration
of Section 50.12.** The coboundary of left multiplication by `ρ(f⁻¹ω)` is left multiplication by
`dρ(f⁻¹ω) = ρ(f⁻¹dω)` (`SheafOfModules.DifferentialGradedAlgebra.δ_restrictedLeftMulCochain` and
`Stacks.DeRhamSmooth.d_pulledBackForm`), so this is
`Stacks.DeRhamSmooth.respectsFiltration_restrictedLeftMulCochain` at the `(p + 1)`-form `dω`. -/
theorem respectsFiltration_δ_restrictedLeftMulCochain (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) :
    CochainComplex.Filtered.RespectsFiltration
      (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
      (deRhamSmoothFiltration f g : CochainComplex.Filtered
        (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))))
      (CochainComplex.HomComplex.δ (p : ℤ) ((p : ℤ) + 1)
        (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
          (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U)
          (deRhamDGA f g) (pulledBackForm f g U p ω))) := by
  have e := (SheafOfModules.DifferentialGradedAlgebra.δ_restrictedLeftMulCochain
    (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g)
    (pulledBackForm f g U p ω)).trans
    (congrArg (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
      (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g))
      (d_pulledBackForm f g U p ω))
  exact cast (congrArg (fun c => CochainComplex.Filtered.RespectsFiltration
      (moduleRestriction (inverseImageBase (f ≫ g)) (pulledBackOpen f g U))
      (deRhamSmoothFiltration f g : CochainComplex.Filtered
        (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g))))) c) e.symm)
    (respectsFiltration_restrictedLeftMulCochain f g U (p + 1)
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω))

end Stacks.DeRhamSmooth

end
