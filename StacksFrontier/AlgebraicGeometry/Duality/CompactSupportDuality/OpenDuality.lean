module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.Linearity
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DegreeZeroCompactSupport
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf

/-!
# Duality on an open over a field: `H^i(U, K) = Hom((D_U K)[-i], ω_U^•)`

Let `p : U ⟶ Spec k` be a Noetherian scheme over a field and `ω` a dualizing complex on `U`, with
`D_U = R𝓗om(-, ω)` the duality of [Stacks, Tag 0A89] on `D^b_{Coh}(𝒪_U)`. The proof of
[Stacks, Tag 0G5A] identifies, for `K ∈ D^b_{Coh}(𝒪_U)`,

`H^i(U, K) = H^0(U, K[i]) = Hom(𝒪_U, K[i]) = Hom(D_U(K[i]), D_U(𝒪_U)) = Hom((D_U K)[-i], ω)`,

`k`-linearly and naturally in `K`. The steps are: `RΓ(U, -)` and `H^0` commute with shifts;
`Hom(𝒪_U, -) = H^0(U, -)` (`AlgebraicGeometry.structureSheafHomLinearEquiv`); `D_U` is fully
faithful on `D^b_{Coh}(𝒪_U)` (`Stacks.Duality.boundedCoherentDuality_isEquivalence`) and carries a
scalar to that scalar (`AlgebraicGeometry.schemeDerivedDualFunctor_map_smul_id`);
`R𝓗om(K[i], ω) = R𝓗om(K, ω)[-i]` (`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso`);
and `R𝓗om(𝒪_U, ω) = ω` (`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`).

## Main definitions

* `AlgebraicGeometry.openDualObj`, `AlgebraicGeometry.openDualMap`: `D_U = R𝓗om(-, ω)` on
  objects and morphisms of `D^b_{Coh}(𝒪_U)`.
* `AlgebraicGeometry.openDualityLinearEquiv`: `H^i(U, K) ≃ₗ[k] Hom((D_U K)[-i], W)` for any
  `W ∈ D^b_{Coh}(𝒪_U)` identified with `ω`.

## Main results

* `AlgebraicGeometry.openDualityLinearEquiv_naturality`: the identification is natural in `K`.

## Implementation notes

The `k`-linear structure on `𝒪_U`-modules is `AlgebraicGeometry.modulesLinear k (Over.mk p)`. It
cannot be a local instance, since `p` does not occur in `Linear k U.Modules`; it is introduced by
`letI` in the statements, as in `AlgebraicGeometry.structureSheafHomLinearEquiv`, and `letI` is
inlined at elaboration, so the statements carry the instance term itself.

The derived categories are at `CategoryTheory.HasDerivedCategory.standard`, the model at which
`Stacks.Duality.boundedCoherentDuality`, `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`
and `AlgebraicGeometry.BoundedCoherentDerived` are used here; it is named in each statement by
`letI`, inlined at elaboration like the `k`-linear structure.

## References

* [Stacks Project, Tag 0G5A](https://stacks.math.columbia.edu/tag/0G5A)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Duality

universe u

namespace AlgebraicGeometry

section Dual

variable {U : Scheme.{u}} [IsNoetherian U]
  (ω : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules))
  (hω : letI := HasDerivedCategory.standard U.Modules; IsDualizingComplex ω)

/-- `D_U K = R𝓗om(K, ω)` as an object of `D^b_{Coh}(𝒪_U)`, for a dualizing complex `ω`
([Stacks, Tag 0A89]). Its underlying object is `AlgebraicGeometry.RingedSite.derivedDualInto`. -/
def openDualObj (K : BoundedCoherentDerived U) : BoundedCoherentDerived U :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite U.sheaf).O))
  ⟨RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite U.sheaf) ω K.obj,
    derivedCategoryBBounded_derivedSheafHom U hω K.obj K.property⟩

/-- `D_U = R𝓗om(-, ω)` on morphisms of `D^b_{Coh}(𝒪_U)`. -/
def openDualMap {K K' : BoundedCoherentDerived U} (f : K ⟶ K') :
    openDualObj ω hω K' ⟶ openDualObj ω hω K :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite U.sheaf).O))
  ObjectProperty.homMk
    (((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite U.sheaf)).map
      f.hom.op).app ω)

/-- The underlying morphism of `D_U f` is `R𝓗om(f, ω)`. -/
theorem openDualMap_hom {K K' : BoundedCoherentDerived U} (f : K ⟶ K') :
    letI := HasDerivedCategory.standard U.Modules
    (openDualMap ω hω f).hom = (schemeDerivedDualFunctor ω).map f.hom.op := rfl

/-- `D_U` is a contravariant functor. -/
theorem openDualMap_comp {K K' K'' : BoundedCoherentDerived U} (f : K ⟶ K') (g : K' ⟶ K'') :
    openDualMap ω hω (f ≫ g) = openDualMap ω hω g ≫ openDualMap ω hω f :=
  let _ := HasDerivedCategory.standard U.Modules
  (boundedCoherentDuality U hω).map_comp (X := op ⟨K''.obj, K''.property⟩)
    (Y := op ⟨K'.obj, K'.property⟩) (Z := op ⟨K.obj, K.property⟩)
    (ObjectProperty.homMk g.hom).op (ObjectProperty.homMk f.hom).op

/-- `D_U` is fully faithful on `D^b_{Coh}(𝒪_U)`: it is an anti-equivalence
([Stacks, Tag 0A89]). -/
def openDualFullyFaithful :
    letI := HasDerivedCategory.standard U.Modules
    (boundedCoherentDuality U hω).FullyFaithful :=
  letI := HasDerivedCategory.standard U.Modules
  haveI := boundedCoherentDuality_isEquivalence U hω
  Functor.FullyFaithful.ofFullyFaithful _

/-- `R𝓗om(E[i], ω) ≅ R𝓗om(E, ω)[-i]`, in the scheme's spelling of `D(𝒪_U)`. -/
def schemeDerivedDualShiftIso
    (E : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules)) (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    (schemeDerivedDualFunctor ω).obj (op (E⟦i⟧)) ≅
      ((schemeDerivedDualFunctor ω).obj (op E))⟦-i⟧ :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite U.sheaf).O))
  RingedSite.derivedSheafHomSourceShiftIso (Stacks.SheafOfModules.ringedSite U.sheaf) E ω i

omit [IsNoetherian U] in
/-- `R𝓗om(E[i], ω) ≅ R𝓗om(E, ω)[-i]` is natural in `E`. -/
theorem schemeDerivedDualShiftIso_hom_naturality
    {E E' : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules)}
    (φ : E ⟶ E') (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    (schemeDerivedDualFunctor ω).map (φ⟦i⟧').op ≫ (schemeDerivedDualShiftIso ω E i).hom =
      (schemeDerivedDualShiftIso ω E' i).hom ≫ ((schemeDerivedDualFunctor ω).map φ.op)⟦-i⟧' :=
  let _ := HasDerivedCategory.standard U.Modules
  let _ := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite U.sheaf).O))
  RingedSite.derivedSheafHomSourceShiftIso_hom_naturality_left
    (Stacks.SheafOfModules.ringedSite U.sheaf) ω φ i

/-- `D_U(K[i]) ≅ (D_U K)[-i]` in `D^b_{Coh}(𝒪_U)`. -/
def openDualShiftIso (K : BoundedCoherentDerived U) (i : ℤ) :
    openDualObj ω hω (K⟦i⟧) ≅ (openDualObj ω hω K)⟦-i⟧ :=
  letI := HasDerivedCategory.standard U.Modules
  (boundedCoherentDerived U).fullyFaithfulι.preimageIso
    (((schemeDerivedDualFunctor ω).mapIso
        (((boundedCoherentDerived U).ι.commShiftIso i).app K).op).symm ≪≫
      schemeDerivedDualShiftIso ω K.obj i ≪≫
      (((boundedCoherentDerived U).ι.commShiftIso (-i)).app (openDualObj ω hω K)).symm)

/-- The underlying morphism of `D_U(K[i]) ≅ (D_U K)[-i]`. -/
theorem ι_map_openDualShiftIso_hom (K : BoundedCoherentDerived U) (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    (boundedCoherentDerived U).ι.map (openDualShiftIso ω hω K i).hom =
      (schemeDerivedDualFunctor ω).map
          (((boundedCoherentDerived U).ι.commShiftIso i).inv.app K).op ≫
        (schemeDerivedDualShiftIso ω K.obj i).hom ≫
        ((boundedCoherentDerived U).ι.commShiftIso (-i)).inv.app (openDualObj ω hω K) :=
  let _ := HasDerivedCategory.standard U.Modules
  (boundedCoherentDerived U).fullyFaithfulι.map_preimage _

/-- `D_U(K[i]) ≅ (D_U K)[-i]` is natural in `K`. -/
theorem openDualShiftIso_hom_naturality {K K' : BoundedCoherentDerived U} (α : K ⟶ K') (i : ℤ) :
    openDualMap ω hω (α⟦i⟧') ≫ (openDualShiftIso ω hω K i).hom =
      (openDualShiftIso ω hω K' i).hom ≫ (openDualMap ω hω α)⟦-i⟧' := by
  let _ := HasDerivedCategory.standard U.Modules
  let P := boundedCoherentDerived U
  let D := schemeDerivedDualFunctor ω
  have h1 : (P.ι.map α)⟦i⟧' ≫ (P.ι.commShiftIso i).inv.app K' =
      (P.ι.commShiftIso i).inv.app K ≫ P.ι.map (α⟦i⟧') :=
    Functor.commShiftIso_inv_naturality P.ι α i
  have h2 :=
    schemeDerivedDualShiftIso_hom_naturality ω (E := K.obj) (E' := K'.obj) (P.ι.map α) i
  have h3 : (D.map (P.ι.map α).op)⟦-i⟧' ≫
        (P.ι.commShiftIso (-i)).inv.app (openDualObj ω hω K) =
      (P.ι.commShiftIso (-i)).inv.app (openDualObj ω hω K') ≫
        P.ι.map ((openDualMap ω hω α)⟦-i⟧') :=
    Functor.commShiftIso_inv_naturality P.ι (openDualMap ω hω α) (-i)
  apply P.fullyFaithfulι.map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_openDualShiftIso_hom,
    ι_map_openDualShiftIso_hom]
  have e1 : D.map (P.ι.map (α⟦i⟧')).op ≫ D.map ((P.ι.commShiftIso i).inv.app K).op =
      D.map ((P.ι.commShiftIso i).inv.app K').op ≫ D.map ((P.ι.map α)⟦i⟧').op := by
    rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp, h1]
  refine (Category.assoc _ _ _).symm.trans ((e1 =≫ _).trans ?_)
  refine (Category.assoc _ _ _).trans ((_ ≫= ((Category.assoc _ _ _).symm.trans
    ((h2 =≫ _).trans ((Category.assoc _ _ _).trans (_ ≫= h3))))).trans
      ((_ ≫= (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm))

/-- `D_U(K[i]) ≅ (D_U K)[-i]` is natural in `K`, for the inverse. -/
theorem openDualShiftIso_inv_naturality {K K' : BoundedCoherentDerived U} (α : K ⟶ K') (i : ℤ) :
    (openDualShiftIso ω hω K' i).inv ≫ openDualMap ω hω (α⟦i⟧') =
      (openDualMap ω hω α)⟦-i⟧' ≫ (openDualShiftIso ω hω K i).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, openDualShiftIso_hom_naturality]

end Dual

section Linear

variable {k : Type u} [Field k] {U : Scheme.{u}} [IsNoetherian U]
  (p : U ⟶ Spec (CommRingCat.of k))
  (ω : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules))
  (hω : letI := HasDerivedCategory.standard U.Modules; IsDualizingComplex ω)

/-- `D_U` is additive. -/
theorem openDualMap_add {A B : BoundedCoherentDerived U} (f g : A ⟶ B) :
    openDualMap ω hω (f + g) = openDualMap ω hω f + openDualMap ω hω g := by
  let _ := HasDerivedCategory.standard U.Modules
  let _ := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite U.sheaf).O))
  have : (schemeDerivedDualFunctor ω).Additive :=
    RingedSite.additive_derivedSheafHom_flip_obj (Stacks.SheafOfModules.ringedSite U.sheaf) ω
  ext
  exact (schemeDerivedDualFunctor ω).map_add (f := f.hom.op) (g := g.hom.op)

/-- `D_U` is `k`-linear. -/
theorem openDualMap_smul (a : k) {A B : BoundedCoherentDerived U} (f : A ⟶ B) :
    letI := HasDerivedCategory.standard U.Modules
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    openDualMap ω hω (a • f) = a • openDualMap ω hω f := by
  let _ := HasDerivedCategory.standard U.Modules
  let : Linear k U.Modules := modulesLinear k (Over.mk p)
  ext
  change (schemeDerivedDualFunctor ω).map (a • f.hom).op =
    a • (schemeDerivedDualFunctor ω).map f.hom.op
  rw [show a • f.hom = (a • 𝟙 A.obj) ≫ f.hom by rw [Linear.smul_comp, Category.id_comp],
    op_comp, Functor.map_comp, schemeDerivedDualFunctor_map_smul_id p A.obj ω a,
    Linear.comp_smul, Category.comp_id]

/-- `Hom(A, B) = Hom(D_U B, D_U A)` on `D^b_{Coh}(𝒪_U)`, `k`-linearly. -/
def openDualHomLinearEquiv (A B : BoundedCoherentDerived U) :
    letI := HasDerivedCategory.standard U.Modules
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    (A ⟶ B) ≃ₗ[k] (openDualObj ω hω B ⟶ openDualObj ω hω A) :=
  letI := HasDerivedCategory.standard U.Modules
  letI : Linear k U.Modules := modulesLinear k (Over.mk p)
  { toFun := openDualMap ω hω
    map_add' := openDualMap_add ω hω
    map_smul' := fun a f => openDualMap_smul p ω hω a f
    invFun := fun h => ((openDualFullyFaithful ω hω).preimage (X := op ⟨B.obj, B.property⟩)
      (Y := op ⟨A.obj, A.property⟩) h).unop
    left_inv := fun f => congrArg Quiver.Hom.unop ((openDualFullyFaithful ω hω).preimage_map
      (X := op ⟨B.obj, B.property⟩) (Y := op ⟨A.obj, A.property⟩) (ObjectProperty.homMk f.hom).op)
    right_inv := fun h => (openDualFullyFaithful ω hω).map_preimage
      (X := op ⟨B.obj, B.property⟩) (Y := op ⟨A.obj, A.property⟩) h }

/-- `H^0(U, K[i]) ≅ H^i(U, K)`, from the commutation of `RΓ(U, -)` and of cohomology with the
shift. -/
def openDualityCohomologyShiftIso (K : BoundedCoherentDerived U) (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((derivedGlobalSectionsOver p).obj (K⟦i⟧).obj) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj) :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
      ((derivedGlobalSectionsOver p).mapIso (((boundedCoherentDerived U).ι.commShiftIso i).app K) ≪≫
        ((derivedGlobalSectionsOver p).commShiftIso i).app K.obj) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso i 0 i (add_zero i)).app _

omit [IsNoetherian U] in
/-- `H^0(U, K[i]) ≅ H^i(U, K)` is natural in `K`. -/
theorem openDualityCohomologyShiftIso_hom_naturality {K K' : BoundedCoherentDerived U}
    (α : K ⟶ K') (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver p).map (α⟦i⟧').hom) ≫
        (openDualityCohomologyShiftIso p K' i).hom =
      (openDualityCohomologyShiftIso p K i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
          ((derivedGlobalSectionsOver p).map α.hom) := by
  let _ := HasDerivedCategory.standard U.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  let P := boundedCoherentDerived U
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let R := derivedGlobalSectionsOver p
  have h1 : P.ι.map (α⟦i⟧') ≫ (P.ι.commShiftIso i).hom.app K' =
      (P.ι.commShiftIso i).hom.app K ≫ (P.ι.map α)⟦i⟧' :=
    Functor.commShiftIso_hom_naturality P.ι α i
  have h2 : R.map ((P.ι.map α)⟦i⟧') ≫ (R.commShiftIso i).hom.app K'.obj =
      (R.commShiftIso i).hom.app K.obj ≫ (R.map (P.ι.map α))⟦i⟧' :=
    Functor.commShiftIso_hom_naturality R (P.ι.map α) i
  have h3 : H.map ((R.map (P.ι.map α))⟦i⟧') ≫
        (H.shiftIso i 0 i (add_zero i)).hom.app (R.obj K'.obj) =
      (H.shiftIso i 0 i (add_zero i)).hom.app (R.obj K.obj) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map (R.map (P.ι.map α)) :=
    H.shiftIso_hom_naturality i 0 i (add_zero i) (R.map (P.ι.map α))
  have e1 : H.map (R.map (P.ι.map (α⟦i⟧'))) ≫ H.map (R.map ((P.ι.commShiftIso i).hom.app K')) ≫
        H.map ((R.commShiftIso i).hom.app K'.obj) =
      H.map (R.map ((P.ι.commShiftIso i).hom.app K)) ≫ H.map ((R.commShiftIso i).hom.app K.obj) ≫
        H.map ((R.map (P.ι.map α))⟦i⟧') := by
    rw [← H.map_comp, ← H.map_comp, ← H.map_comp, ← H.map_comp,
      ← Category.assoc (R.map (P.ι.map (α⟦i⟧'))), ← R.map_comp, h1, R.map_comp,
      Category.assoc, h2]
  change H.map (R.map (P.ι.map (α⟦i⟧'))) ≫ (H.map (R.map ((P.ι.commShiftIso i).hom.app K') ≫
      (R.commShiftIso i).hom.app K'.obj) ≫
        (H.shiftIso i 0 i (add_zero i)).hom.app (R.obj K'.obj)) =
    (H.map (R.map ((P.ι.commShiftIso i).hom.app K) ≫ (R.commShiftIso i).hom.app K.obj) ≫
        (H.shiftIso i 0 i (add_zero i)).hom.app (R.obj K.obj)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map (R.map (P.ι.map α))
  rw [H.map_comp, H.map_comp]
  exact ((Category.assoc _ _ _).symm.trans (e1 =≫ _)).trans ((Category.assoc _ _ _).trans
    ((_ ≫= (Category.assoc _ _ _)).trans ((_ ≫= (_ ≫= h3)).trans
      ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm))))

omit [IsNoetherian U] in
/-- `H^0(U, K[i]) ≅ H^i(U, K)` is natural in `K`, for the inverse. -/
theorem openDualityCohomologyShiftIso_inv_naturality {K K' : BoundedCoherentDerived U}
    (α : K ⟶ K') (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
          ((derivedGlobalSectionsOver p).map α.hom) ≫
        (openDualityCohomologyShiftIso p K' i).inv =
      (openDualityCohomologyShiftIso p K i).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver p).map (α⟦i⟧').hom) := by
  rw [Iso.comp_inv_eq, Category.assoc, openDualityCohomologyShiftIso_hom_naturality,
    Iso.inv_hom_id_assoc]

omit [IsNoetherian U] in
/-- `H^0(U, E) = Hom(𝒪_U, E)` is natural in `E`: the map induced by `φ` on `H^0` is
postcomposition with `φ`. -/
theorem structureSheafHomLinearEquiv_symm_naturality
    {E E' : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules)}
    (φ : E ⟶ E')
    (y :
      letI := HasDerivedCategory.standard U.Modules
      letI := HasDerivedCategory.standard (ModuleCat.{u} k)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((derivedGlobalSectionsOver p).obj E)) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    (structureSheafHomLinearEquiv p E').symm
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver p).map φ)).hom y) =
      (structureSheafHomLinearEquiv p E).symm y ≫ φ := by
  let _ := HasDerivedCategory.standard U.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  rw [LinearEquiv.symm_apply_eq]
  change _ = structureSheafHomAddEquiv p E' ((structureSheafHomLinearEquiv p E).symm y ≫ φ)
  rw [structureSheafHomAddEquiv_comp]
  exact congrArg _ (LinearEquiv.apply_symm_apply (structureSheafHomLinearEquiv p E) y).symm

/-- `Hom(𝒪_U, B)` in `D(𝒪_U)` and in `D^b_{Coh}(𝒪_U)`. -/
def openDualityUnitHomLinearEquiv (B : BoundedCoherentDerived U) :
    letI := HasDerivedCategory.standard U.Modules
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    (derivedUnitObject U ⟶ B.obj) ≃ₗ[k] (structureSheafBoundedCoherent U ⟶ B) :=
  letI := HasDerivedCategory.standard U.Modules
  letI : Linear k U.Modules := modulesLinear k (Over.mk p)
  { toFun := fun g => ObjectProperty.homMk g
    invFun := fun f => f.hom
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `Hom(𝒪_U, B)` in `D(𝒪_U)` and in `D^b_{Coh}(𝒪_U)` is natural in `B`. -/
theorem openDualityUnitHomLinearEquiv_comp {B B' : BoundedCoherentDerived U}
    (g : letI := HasDerivedCategory.standard U.Modules; derivedUnitObject U ⟶ B.obj) (β : B ⟶ B') :
    letI := HasDerivedCategory.standard U.Modules
    openDualityUnitHomLinearEquiv p B' (g ≫ β.hom) = openDualityUnitHomLinearEquiv p B g ≫ β :=
  rfl

end Linear

section Structure

variable {U : Scheme.{u}} [IsNoetherian U]
  (ω : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules))
  (hω : letI := HasDerivedCategory.standard U.Modules; IsDualizingComplex ω)

/-- `D_U 𝒪_U = R𝓗om(𝒪_U, ω) ≅ ω ≅ W` in `D^b_{Coh}(𝒪_U)`. -/
def openDualStructureSheafIso (W : BoundedCoherentDerived U) (eW : W.obj ≅ ω) :
    openDualObj ω hω (structureSheafBoundedCoherent U) ≅ W :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite U.sheaf).O))
  (boundedCoherentDerived U).fullyFaithfulι.preimageIso
    (show (boundedCoherentDerived U).ι.obj (openDualObj ω hω (structureSheafBoundedCoherent U)) ≅
        (boundedCoherentDerived U).ι.obj W from
      RingedSite.derivedStructureSheafHomIso (Stacks.SheafOfModules.ringedSite U.sheaf) ω ≪≫
        eW.symm)

end Structure

section Main

variable {k : Type u} [Field k] {U : Scheme.{u}} [IsNoetherian U]
  (p : U ⟶ Spec (CommRingCat.of k))
  (ω : @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules))
  (hω : letI := HasDerivedCategory.standard U.Modules; IsDualizingComplex ω)

/-- **`H^i(U, K) = Hom((D_U K)[-i], ω_U^•)`**, the identification on `U` in the proof of
[Stacks, Tag 0G5A], `k`-linearly, for any `W ∈ D^b_{Coh}(𝒪_U)` identified with the dualizing
complex `ω`: `H^i(U, K) = H^0(U, K[i]) = Hom(𝒪_U, K[i]) = Hom(D_U(K[i]), D_U 𝒪_U) =
Hom((D_U K)[-i], W)`. -/
def openDualityLinearEquiv (W : BoundedCoherentDerived U) (eW : W.obj ≅ ω)
    (K : BoundedCoherentDerived U) (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    letI : Linear k U.Modules := modulesLinear k (Over.mk p)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj)) ≃ₗ[k]
      ((openDualObj ω hω K)⟦-i⟧ ⟶ W) :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  letI : Linear k U.Modules := modulesLinear k (Over.mk p)
  (openDualityCohomologyShiftIso p K i).symm.toLinearEquiv ≪≫ₗ
    (structureSheafHomLinearEquiv p (K⟦i⟧).obj).symm ≪≫ₗ
    openDualityUnitHomLinearEquiv p (K⟦i⟧) ≪≫ₗ
    openDualHomLinearEquiv p ω hω (structureSheafBoundedCoherent U) (K⟦i⟧) ≪≫ₗ
    Linear.homCongr k (openDualShiftIso ω hω K i) (openDualStructureSheafIso ω hω W eW)

/-- The identification `H^i(U, K) = Hom((D_U K)[-i], W)` on an element. -/
theorem openDualityLinearEquiv_apply (W : BoundedCoherentDerived U) (eW : W.obj ≅ ω)
    (K : BoundedCoherentDerived U) (i : ℤ)
    (x :
      letI := HasDerivedCategory.standard U.Modules
      letI := HasDerivedCategory.standard (ModuleCat.{u} k)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
      ((derivedGlobalSectionsOver p).obj K.obj)) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    openDualityLinearEquiv p ω hω W eW K i x =
      ((openDualShiftIso ω hω K i).inv ≫
        openDualMap ω hω (openDualityUnitHomLinearEquiv p (K⟦i⟧)
          ((structureSheafHomLinearEquiv p (K⟦i⟧).obj).symm
            ((openDualityCohomologyShiftIso p K i).inv.hom x)))) ≫
        (openDualStructureSheafIso ω hω W eW).hom :=
  rfl

/-- **`H^i(U, K) = Hom((D_U K)[-i], W)` is natural in `K`**: the map induced by `α : K ⟶ K'` on
`H^i(U, -)` corresponds to precomposition with `(D_U α)[-i]`. -/
theorem openDualityLinearEquiv_naturality (W : BoundedCoherentDerived U) (eW : W.obj ≅ ω)
    {K K' : BoundedCoherentDerived U} (α : K ⟶ K') (i : ℤ)
    (x :
      letI := HasDerivedCategory.standard U.Modules
      letI := HasDerivedCategory.standard (ModuleCat.{u} k)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
      ((derivedGlobalSectionsOver p).obj K.obj)) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    openDualityLinearEquiv p ω hω W eW K' i
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
          ((derivedGlobalSectionsOver p).map α.hom)).hom x) =
      (openDualMap ω hω α)⟦-i⟧' ≫ openDualityLinearEquiv p ω hω W eW K i x := by
  let _ := HasDerivedCategory.standard U.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  rw [openDualityLinearEquiv_apply, openDualityLinearEquiv_apply]
  have h1 : (openDualityCohomologyShiftIso p K' i).inv.hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
          ((derivedGlobalSectionsOver p).map α.hom)).hom x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver p).map (α⟦i⟧').hom)).hom
        ((openDualityCohomologyShiftIso p K i).inv.hom x) :=
    congrArg (fun f => f.hom x) (openDualityCohomologyShiftIso_inv_naturality p α i)
  rw [h1, structureSheafHomLinearEquiv_symm_naturality, openDualityUnitHomLinearEquiv_comp,
    openDualMap_comp, reassoc_of% openDualShiftIso_inv_naturality, Category.assoc, Category.assoc]

end Main

end AlgebraicGeometry

end
