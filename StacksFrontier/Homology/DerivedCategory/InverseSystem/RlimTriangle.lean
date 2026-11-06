module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Ab
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# The derived inverse limit as a derived limit

An object of the derived category of inverse systems of abelian groups determines an inverse
system in the derived category of abelian groups, by applying at each index the derived
evaluation functor of `StacksFrontier.Homology.DerivedCategory.InverseSystem.Ab`. The right-derived
inverse-limit functor is a derived limit of that system: its value belongs to the canonical
distinguished triangle `R lim K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ (R lim K)⟦1⟧` whose middle map is
`1 - shift`.

## Main definitions

* `Rlim.derivedEvaluationSystem`: the inverse system in `D(Ab)` associated to an object of
  `D(Ab(N))`, with transition maps the derived evaluation transition transformations.
* `Rlim.homologySystem`: the degreewise cohomology of that evaluated system, an inverse system of
  abelian groups.

## Main results

* `Rlim.lim_hasRightDerivedFunctor_and_isDerivedLimit`: the right-derived inverse limit is a
  derived limit in the sense of the canonical product triangle (Tag 07KX).
* `Rlim.derivedLimit_iso_rightDerivedLimit_and_homology_shortExact`: an inverse system in `D(Ab)`
  lifts to `D(Ab(N))`, the right-derived inverse limit of any lift is a derived limit of the
  system and hence independent of the lift, and the cohomology of that derived limit lies in the
  canonical short exact sequence with outer terms `R¹lim H^(p-1)` and `lim H^p` (Tag 08U5).

## Implementation notes

The evaluated system uses the derived evaluation functors
  `Stacks.InverseSystem.AbelianGroupDerivedLift.evD` and their
transition transformations `Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans`, so it is the
  system to which the lift of
Tag 0CQ9 is compared. The predicate `CategoryTheory.Pretriangulated.IsDerivedLimit` records the
entire distinguished triangle, including the prescribed difference map on the product; the
triangle itself comes from the degreewise short exact sequence
`0 ⟶ lim ⟶ ∏ ⟶ ∏ ⟶ 0` of a termwise right-acyclic representative, and the identification of
its middle term with the product in `D(Ab)` uses that the localization functor preserves
countable products (Stacks 07KC).

## References

* [Stacks Project, Tag 07KX](https://stacks.math.columbia.edu/tag/07KX)
* [Stacks Project, Tag 08U5](https://stacks.math.columbia.edu/tag/08U5)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/


section

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim

universe u

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _

noncomputable local instance : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse system in `D(Ab)` obtained by applying the derived evaluation functors of
Tag 0CQ9 to an object of `D(Ab(N))`. Its maps are the derived evaluation transition maps. -/
public noncomputable def derivedEvaluationSystem
    (K : DerivedCategory Rlim.InvSystemAb.{u}) : ℕᵒᵖ ⥤ DerivedCategory Ab.{u} where
  obj n := (Stacks.InverseSystem.AbelianGroupDerivedLift.evD.{u} n).obj K
  map {a b} f := (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans.{u} f).app K
  map_id X := by rw [Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans_id, NatTrans.id_app]
  map_comp f g := by rw [Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans_comp,
    NatTrans.comp_app]

/-- The degreewise cohomology inverse system associated to a derived inverse system. -/
public noncomputable abbrev homologySystem
    (K : DerivedCategory Rlim.InvSystemAb.{u}) (p : ℤ) : Rlim.InvSystemAb.{u} :=
  derivedEvaluationSystem K ⋙ DerivedCategory.homologyFunctor Ab.{u} p

/-- Identifies a chosen evaluated term with derived evaluation, so morphisms can be compared. -/
public noncomputable abbrev derivedEvaluationComparison
    (K : DerivedCategory Rlim.InvSystemAb.{u}) (n : ℕᵒᵖ) :
    (derivedEvaluationSystem K).obj n ≅
      ((evaluation ℕᵒᵖ Ab.{u}).obj n).mapDerivedCategory.obj K :=
  Iso.refl _

@[simp]
public theorem derivedEvaluationSystem_obj (K : DerivedCategory Rlim.InvSystemAb.{u})
    (n : ℕᵒᵖ) :
    (derivedEvaluationSystem K).obj n = (Stacks.InverseSystem.AbelianGroupDerivedLift.evD.{u} n).obj
      K := rfl

@[simp]
public theorem derivedEvaluationSystem_map (K : DerivedCategory Rlim.InvSystemAb.{u})
    {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (derivedEvaluationSystem K).map f = (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans.{u}
      f).app K := rfl

end Rlim
end

end


section

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rlim

universe u

noncomputable local instance : HasDerivedCategory Ab.{u} := HasDerivedCategory.standard _
noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{u} :=
  HasDerivedCategory.standard _
noncomputable local instance : (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The `n`-th projection of a coordinatewise product map is the `n`-th component of the map.

This is Mathlib's `CategoryTheory.Limits.Pi.map_π` stated at `Rlim.prodMap`, whose reducible body
is what lets the product complex's differential be recognised as such a map. -/
private lemma prodMap_π {A B : Rlim.InvSystemAb.{u}} (f : A ⟶ B) (n : ℕ) :
    Rlim.prodMap f ≫ Pi.π (fun n : ℕ ↦ B.obj (op n)) n =
      Pi.π (fun n : ℕ ↦ A.obj (op n)) n ≫ f.app (op n) :=
  CategoryTheory.Limits.Pi.map_π _ n

private noncomputable def complexShort
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) :
    ShortComplex (CochainComplex Ab.{u} ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex limitToProdNatTrans.{u} (ComplexShape.up ℤ)).app L)
    ((NatTrans.mapHomologicalComplex deltaNatTrans.{u} (ComplexShape.up ℤ)).app L) (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp]
      rw [limitToProdNatTrans_comp_deltaNatTrans]
      rfl)

private lemma complexShort_shortExact
    (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
    (hshort : ∀ A : Rlim.InvSystemAb.{u},
      IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
        (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj A))) →
      ∃ w : Rlim.limitToProduct A ≫ Rlim.delta A = 0,
        (ShortComplex.mk (Rlim.limitToProduct A) (Rlim.delta A) w).ShortExact)
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ)
    (hL : ∀ p : ℤ, IsZero ((DerivedCategory.homologyFunctor Ab.{u} 1).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{u} 0).obj (L.X p))))) :
    (complexShort L).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro p
  obtain ⟨w, hw⟩ := hshort (L.X p) (hL p)
  change (ShortComplex.mk (Rlim.limitToProduct (L.X p))
    (Rlim.delta (L.X p)) _).ShortExact
  exact hw

private noncomputable abbrev evaluatedComplex
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) (n : ℕ) : CochainComplex Ab.{u} ℤ :=
  (((evaluation ℕᵒᵖ Ab.{u}).obj (op n)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L

private noncomputable def productComplexπ
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) (n : ℕ) :
    (productFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶
      evaluatedComplex L n where
  f p := Pi.π (fun n : ℕ ↦ (L.X p).obj (op n)) n
  comm' i j := fun _ ↦ (prodMap_π (L.d i j) n).symm

private noncomputable def productComplexFan
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) :
    Fan (fun n : ℕ ↦ evaluatedComplex L n) :=
  Fan.mk _ (productComplexπ L)

private noncomputable def productComplexFanIsLimit
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) : IsLimit (productComplexFan L) :=
  Fan.IsLimit.mk _ (fun s ↦
    { f := fun p ↦ Pi.lift fun n : ℕ ↦ (s.proj n).f p
      comm' := fun i j ↦ by
        intro hij
        apply Pi.hom_ext
        intro n
        change (Pi.lift fun n : ℕ ↦ (s.proj n).f i) ≫ Rlim.prodMap (L.d i j) ≫
          Pi.π (fun n : ℕ ↦ (L.X j).obj (op n)) n = _
        rw [Category.assoc, prodMap_π, ← Category.assoc]
        erw [Pi.lift_comp_π]
        simp only [Pi.lift_comp_π]
        exact (s.proj n).comm i j })
    (fun s n ↦ by
      ext p : 1
      change (Pi.lift (fun n ↦ (s.proj n).f p)) ≫
        Pi.π (fun n ↦ (L.X p).obj (op n)) n = _
      exact Pi.lift_comp_π _ n)
    (fun s m hm ↦ by
      ext p : 1
      apply Pi.hom_ext
      intro n
      simpa only [Category.assoc, Pi.lift_comp_π, HomologicalComplex.comp_f,
        productComplexFan, fan_mk_proj, productComplexπ] using
        congrArg (fun k ↦ k.f p) (hm n))

private noncomputable abbrev evaluatedTransition
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) {a b : ℕ}
    (f : op a ⟶ op b) : evaluatedComplex L a ⟶ evaluatedComplex L b :=
  (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ Ab.{u}).map f)
    (ComplexShape.up ℤ)).app L

private noncomputable abbrev evaluationFactors
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) (n : ℕ) :
    (derivedEvaluationSystem (Q.obj L)).obj (op n) ≅ Q.obj (evaluatedComplex L n) :=
  (((evaluation ℕᵒᵖ Ab.{u}).obj (op n)).mapDerivedCategoryFactors).app L

/-- The isomorphism between the derived evaluation system at an index and the derived category
object of the evaluated complex is natural in the index. -/
public lemma evaluationFactors_naturality
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) {n m : ℕᵒᵖ} (a : n ⟶ m) :
    (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans a).app (Q.obj L) ≫
        ((evaluation ℕᵒᵖ Ab.{u}).obj m).mapDerivedCategoryFactors.hom.app L =
      ((evaluation ℕᵒᵖ Ab.{u}).obj n).mapDerivedCategoryFactors.hom.app L ≫
        Q.map ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ Ab.{u}).map a)
          (ComplexShape.up ℤ)).app L) := by
  rw [Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans, Localization.liftNatTrans_app]
  change (_ ≫ _ ≫ ((evaluation ℕᵒᵖ Ab.{u}).obj m).mapDerivedCategoryFactors.inv.app L) ≫
    ((evaluation ℕᵒᵖ Ab.{u}).obj m).mapDerivedCategoryFactors.hom.app L = _
  simp
  rfl

private noncomputable abbrev evaluationIso
    {K : DerivedCategory Rlim.InvSystemAb.{u}}
    {L : CochainComplex Rlim.InvSystemAb.{u} ℤ} (e : K ≅ Q.obj L) (n : ℕ) :
    (derivedEvaluationSystem K).obj (op n) ≅ Q.obj (evaluatedComplex L n) :=
  (Stacks.InverseSystem.AbelianGroupDerivedLift.evD (op n)).mapIso e ≪≫ evaluationFactors L n

private lemma evaluationIso_naturality
    {K : DerivedCategory Rlim.InvSystemAb.{u}}
    {L : CochainComplex Rlim.InvSystemAb.{u} ℤ} (e : K ≅ Q.obj L)
    {a b : ℕ} (f : op a ⟶ op b) :
    (derivedEvaluationSystem K).map f ≫ (evaluationIso e b).hom =
      (evaluationIso e a).hom ≫ Q.map (evaluatedTransition L f) := by
  change (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans f).app K ≫
    (Stacks.InverseSystem.AbelianGroupDerivedLift.evD (op b)).map e.hom ≫ (evaluationFactors L
      b).hom = _
  rw [← Category.assoc, ← NatTrans.naturality, Category.assoc]
  rw [show (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans f).app (Q.obj L) ≫
      (evaluationFactors L b).hom =
        (evaluationFactors L a).hom ≫ Q.map (evaluatedTransition L f)
    from evaluationFactors_naturality L f]
  simp only [evaluationIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]

private lemma evaluationIso_inv_naturality
    {K : DerivedCategory Rlim.InvSystemAb.{u}}
    {L : CochainComplex Rlim.InvSystemAb.{u} ℤ} (e : K ≅ Q.obj L)
    {a b : ℕ} (f : op a ⟶ op b) :
    Q.map (evaluatedTransition L f) ≫ (evaluationIso e b).inv =
      (evaluationIso e a).inv ≫ (derivedEvaluationSystem K).map f := by
  apply (cancel_mono (evaluationIso e b).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [evaluationIso_naturality, Iso.inv_hom_id_assoc]

private lemma complexShort_g_π
    (L : CochainComplex Rlim.InvSystemAb.{u} ℤ) (n : ℕ) :
    (complexShort L).g ≫ productComplexπ L n = productComplexπ L n -
      productComplexπ L (n + 1) ≫ evaluatedTransition L (homOfLE (Nat.le_succ n)).op := by
  ext p : 1
  change (Rlim.delta (L.X p)) ≫ Pi.π (fun n ↦ (L.X p).obj (op n)) n =
    Pi.π (fun n ↦ (L.X p).obj (op n)) n -
      Pi.π (fun n ↦ (L.X p).obj (op n)) (n + 1) ≫ (L.X p).map _
  simp [Rlim.delta, Rlim.shift, Preadditive.sub_comp]

private noncomputable abbrev derivedProductFan
    {K : DerivedCategory Rlim.InvSystemAb.{u}}
    {L : CochainComplex Rlim.InvSystemAb.{u} ℤ} (e : K ≅ Q.obj L) :
    Fan (fun n : ℕ ↦ (derivedEvaluationSystem K).obj (op n)) :=
  Fan.mk (Q.obj (complexShort L).X₂)
    (fun n ↦ Q.map (productComplexπ L n) ≫ (evaluationIso e n).inv)

private noncomputable def derivedProductFanIsLimit
    {K : DerivedCategory Rlim.InvSystemAb.{u}}
    {L : CochainComplex Rlim.InvSystemAb.{u} ℤ} (e : K ≅ Q.obj L) :
    IsLimit (derivedProductFan e) := by
  letI := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := Ab.{u}) (I := ℕ)
  let h : IsLimit (Fan.mk (Q.obj (complexShort L).X₂)
      (fun n ↦ Q.map (productComplexπ L n))) :=
    Fan.isLimitMapConeEquiv Q _ _ (isLimitOfPreserves Q (productComplexFanIsLimit L))
  let ei : Discrete.functor (fun n ↦ (derivedEvaluationSystem K).obj (op n)) ≅
      Discrete.functor (fun n ↦ Q.obj (evaluatedComplex L n)) :=
    Discrete.natIso (fun n ↦ evaluationIso e n.as)
  exact (IsLimit.postcomposeInvEquiv ei _).symm h

private lemma derivedProductFan_delta_π
    {K : DerivedCategory Rlim.InvSystemAb.{u}}
    {L : CochainComplex Rlim.InvSystemAb.{u} ℤ} (e : K ≅ Q.obj L) (n : ℕ) :
    Q.map (complexShort L).g ≫ (derivedProductFan e).proj n =
      (derivedProductFan e).proj n - (derivedProductFan e).proj (n + 1) ≫
        (derivedEvaluationSystem K).map (homOfLE (Nat.le_succ n)).op := by
  change Q.map (complexShort L).g ≫ (Q.map (productComplexπ L n) ≫ _) = _
  rw [← Category.assoc, ← Q.map_comp, complexShort_g_π, Q.map_sub, Q.map_comp,
    Preadditive.sub_comp, Category.assoc, evaluationIso_inv_naturality]
  simp only [derivedProductFan, fan_mk_proj, Category.assoc]

open Pretriangulated in
private lemma isDerivedLimit_of_isLimit_fan
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) {P X Y : D} (π : ∀ n : ℕ, P ⟶ F.obj (op n))
    (hπ : IsLimit (Fan.mk P π)) (p : X ⟶ P) (d : P ⟶ P) (δ : P ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p d δ ∈ distTriang D)
    (hd : ∀ n, d ≫ π n = π n - π (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
    (e : Y ≅ X) :
    ∃ _ : HasProduct (fun n : ℕ ↦ F.obj (op n)), IsDerivedLimit F Y := by
  let : HasProduct (fun n : ℕ ↦ F.obj (op n)) := ⟨⟨_, hπ⟩⟩
  refine ⟨inferInstance, ?_⟩
  let eP : P ≅ ∏ᶜ (fun n : ℕ ↦ F.obj (op n)) :=
    hπ.conePointUniqueUpToIso (limit.isLimit _)
  have heP (n : ℕ) : eP.hom ≫ Pi.π (fun n : ℕ ↦ F.obj (op n)) n = π n :=
    hπ.conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨n⟩
  refine ⟨e.hom ≫ p ≫ eP.hom, eP.inv ≫ δ ≫ (shiftFunctor D (1 : ℤ)).map e.inv, ?_⟩
  apply isomorphic_distinguished _ hT
  refine (Triangle.isoMk _ _ e.symm eP eP ?_ ?_ ?_).symm
  · simp
  · dsimp
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub]
    rw [heP, ← Category.assoc, heP]
    exact hd n
  · dsimp
    simp

/-- **Stacks 07KX.** The right-derived inverse-limit functor on inverse systems of abelian groups
is, on every object, a derived limit of the associated inverse system in `D(Ab)`. Equivalently,
its value fits in the canonical distinguished triangle
`R lim K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ (R lim K)⟦1⟧`, where the middle map is
`1 - shift`. -/
@[stacks 07KX]
public theorem lim_hasRightDerivedFunctor_and_isDerivedLimit :
    let F : Rlim.InvSystemAb.{u} ⥤ Ab.{u} := lim
    ∃ (RF : DerivedCategory Rlim.InvSystemAb.{u} ⥤ DerivedCategory Ab.{u})
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso Rlim.InvSystemAb.{u} (ComplexShape.up ℤ)) ∧
      ∀ K : DerivedCategory Rlim.InvSystemAb.{u},
        ∃ _ : HasProduct fun n : ℕ => (derivedEvaluationSystem K).obj (Opposite.op n),
          Pretriangulated.IsDerivedLimit (derivedEvaluationSystem K) (RF.obj K) := by
  obtain ⟨RF, α, hRF, _, _, _, hreplace, hcompute, _, _, hshort, _⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{u}
  refine ⟨RF, α, hRF, ?_⟩
  intro K
  obtain ⟨L, f, hf, hL⟩ := hreplace (Q.objPreimage K)
  have := hf
  let e : K ≅ Q.obj L := (Q.objObjPreimageIso K).symm ≪≫ asIso (Q.map f)
  obtain ⟨eLim⟩ := hcompute L hL
  let hSES := complexShort_shortExact RF hshort L hL
  exact isDerivedLimit_of_isLimit_fan (derivedEvaluationSystem K)
    (derivedProductFan e).proj (derivedProductFanIsLimit e)
    (Q.map (complexShort L).f) (Q.map (complexShort L).g)
    (triangleOfSESδ hSES) (triangleOfSES_distinguished hSES)
    (derivedProductFan_delta_π e) (RF.mapIso e ≪≫ eLim)

end Rlim

end

end


section

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace Rlim

universe v v' u u'

set_option backward.isDefEq.respectTransparency false

noncomputable local instance : (lim : Functor Rlim.InvSystemAb Ab.{0}).Additive :=
  Functor.additive_of_preserves_binary_products _

noncomputable local instance : HasProductsOfShape ℕ (DerivedCategory Ab.{0}) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

private lemma derivedLimit_iso {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : Functor ℕᵒᵖ D) [HasProduct fun n : ℕ => F.obj (Opposite.op n)]
    (K L : D) (hK : Pretriangulated.IsDerivedLimit F K)
    (hL : Pretriangulated.IsDerivedLimit F L) : Nonempty (K ≅ L) := by
  obtain ⟨aK, bK, hTK⟩ := hK
  obtain ⟨aL, bL, hTL⟩ := hL
  let P := ∏ᶜ fun n : ℕ => F.obj (Opposite.op n)
  let d : P ⟶ P := Pi.lift fun n : ℕ =>
    Pi.π (fun n : ℕ => F.obj (Opposite.op n)) n -
      Pi.π (fun n : ℕ => F.obj (Opposite.op n)) (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op
  let TK := Pretriangulated.Triangle.mk aK d bK
  let TL := Pretriangulated.Triangle.mk aL d bL
  obtain ⟨f, hf₁, hf₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    TK TL hTK hTL (𝟙 P) (𝟙 P) (by change d ≫ 𝟙 P = 𝟙 P ≫ d; simp)
  let φ : TK ⟶ TL :=
    { hom₁ := f
      hom₂ := 𝟙 P
      hom₃ := 𝟙 P
      comm₁ := hf₁
      comm₂ := by change d ≫ 𝟙 P = 𝟙 P ≫ d; simp
      comm₃ := hf₂ }
  have : IsIso φ.hom₁ := Pretriangulated.isIso₁_of_isIso₂₃ φ hTK hTL
    (by change IsIso (𝟙 P); infer_instance) (by change IsIso (𝟙 P); infer_instance)
  exact ⟨asIso f⟩

private lemma map_pi_lift_comp_piComparison {A : Type u'} {D : Type u}
    [Category.{v'} A] [Category.{v} D] (H : Functor D A) (X : ℕ → D)
    [HasProduct X] [HasProduct fun n => H.obj (X n)] {Y : D} (w : ∀ n, Y ⟶ X n) :
    H.map (Pi.lift w) ≫ piComparison H X = Pi.lift fun n => H.map (w n) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← H.map_comp, Pi.lift_comp_π, Pi.lift_comp_π]

private lemma map_pi_lift_sub_comp_piComparison {A : Type u'} {D : Type u}
    [Category.{v'} A] [Preadditive A] [Category.{v} D] [Preadditive D]
    (H : Functor D A) [H.Additive] (X : ℕ → D)
    [HasProduct X] [HasProduct fun n => H.obj (X n)] (τ : ∀ n, X (n + 1) ⟶ X n) :
    H.map (Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ τ n) ≫ piComparison H X =
      piComparison H X ≫ Pi.lift fun n => Pi.π (fun n => H.obj (X n)) n -
        Pi.π (fun n => H.obj (X n)) (n + 1) ≫ H.map (τ n) := by
  rw [map_pi_lift_comp_piComparison]
  apply Pi.hom_ext
  intro n
  rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub,
    piComparison_comp_π, H.map_sub, H.map_comp, ← Category.assoc,
    piComparison_comp_π]

private lemma isDerivedLimit_of_iso {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (E E' : Functor ℕᵒᵖ D)
    [HasProduct fun n : ℕ => E.obj (Opposite.op n)]
    [HasProduct fun n : ℕ => E'.obj (Opposite.op n)] (e : E' ≅ E)
    (K : D) (hK : Pretriangulated.IsDerivedLimit E' K) :
    Pretriangulated.IsDerivedLimit E K := by
  obtain ⟨a, b, hT⟩ := hK
  let P' := ∏ᶜ fun n : ℕ => E'.obj (Opposite.op n)
  let P := ∏ᶜ fun n : ℕ => E.obj (Opposite.op n)
  let de : Discrete.functor (fun n : ℕ => E'.obj (Opposite.op n)) ≅
      Discrete.functor (fun n : ℕ => E.obj (Opposite.op n)) :=
    Discrete.natIso fun n => e.app (Opposite.op n.as)
  let pe : P' ≅ P := HasLimit.isoOfNatIso de
  have peπ (n : ℕ) : pe.hom ≫ Pi.π (fun n => E.obj (Opposite.op n)) n =
      Pi.π (fun n => E'.obj (Opposite.op n)) n ≫ (e.app (Opposite.op n)).hom :=
    HasLimit.isoOfNatIso_hom_π de (Discrete.mk n)
  let d' : P' ⟶ P' := Pi.lift fun n : ℕ => Pi.π _ n - Pi.π _ (n + 1) ≫
    E'.map (homOfLE (Nat.le_succ n)).op
  let d : P ⟶ P := Pi.lift fun n : ℕ => Pi.π _ n - Pi.π _ (n + 1) ≫
    E.map (homOfLE (Nat.le_succ n)).op
  have hd : d' ≫ pe.hom = pe.hom ≫ d := by
    apply Pi.hom_ext
    intro n
    dsimp only [d', d]
    rw [Category.assoc, peπ, ← Category.assoc, Pi.lift_comp_π,
      Preadditive.sub_comp]
    simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub]
    congr 1
    · rw [peπ]
    · have hn : E'.map (homOfLE (Nat.le_succ n)).op ≫
          (e.app (Opposite.op n)).hom =
          (e.app (Opposite.op (n + 1))).hom ≫
            E.map (homOfLE (Nat.le_succ n)).op := e.hom.naturality _
      rw [hn, ← Category.assoc pe.hom, peπ, Category.assoc]
  refine ⟨a ≫ pe.hom, pe.inv ≫ b, ?_⟩
  let T' := Pretriangulated.Triangle.mk (a ≫ pe.hom) d (pe.inv ≫ b)
  let T := Pretriangulated.Triangle.mk a d' b
  let et : T' ≅ T := Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) pe.symm pe.symm
    (by dsimp only [T, T', Pretriangulated.Triangle.mk]; simp) (by
      dsimp [T, T']
      simpa using (congrArg (fun f => pe.inv ≫ f ≫ pe.inv) hd).symm) (by
      dsimp only [T, T', Pretriangulated.Triangle.mk]; simp)
  exact Pretriangulated.isomorphic_distinguished T hT T' et

/-- **Stacks 08U5.** Let `E` be an inverse system in `D(Ab)` and let `K` be a derived
limit of `E`.  The system has a lift to `D(Ab(N))`, and the value on every lift of a
right-derived inverse-limit functor is isomorphic to `K`.  In particular this value is
independent, up to isomorphism, of the chosen lift.

For every `p`, the defining product triangle of `K` induces the canonical short exact sequence
`0 ⟶ R¹ lim H^(p-1)(Eₙ) ⟶ H^p(K) ⟶ lim H^p(Eₙ) ⟶ 0`.  The two maps are
specified by the connecting morphism and the map from `K` to the product, respectively. -/
@[stacks 08U5]
public theorem derivedLimit_iso_rightDerivedLimit_and_homology_shortExact
(E : Functor ℕᵒᵖ (DerivedCategory Ab.{0})) :
    let F : Functor Rlim.InvSystemAb Ab.{0} := lim
    ∃ (RF : Functor (DerivedCategory Rlim.InvSystemAb) (DerivedCategory Ab.{0}))
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso Rlim.InvSystemAb (ComplexShape.up ℤ)) ∧
        (∃ K : DerivedCategory Ab.{0}, Pretriangulated.IsDerivedLimit E K) ∧
        (∃ (M : DerivedCategory Stacks.InverseSystem.AbelianGroupDerivedLift.AbN)
          (ψ : ∀ n, (Stacks.InverseSystem.AbelianGroupDerivedLift.evD n).obj M ≅ E.obj n),
          ∀ ⦃a b : ℕᵒᵖ⦄ (f : a ⟶ b),
            (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans f).app M ≫ (ψ b).hom = (ψ a).hom ≫
              E.map f) ∧
        ∀ (K : DerivedCategory Ab.{0}), Pretriangulated.IsDerivedLimit E K →
        (∀ (M : DerivedCategory Stacks.InverseSystem.AbelianGroupDerivedLift.AbN)
            (ψ : ∀ n, (Stacks.InverseSystem.AbelianGroupDerivedLift.evD n).obj M ≅ E.obj n),
            (∀ ⦃a b : ℕᵒᵖ⦄ (f : a ⟶ b),
              (Stacks.InverseSystem.AbelianGroupDerivedLift.evTrans f).app M ≫ (ψ b).hom = (ψ a).hom
                ≫ E.map f) →
            Nonempty (K ≅ RF.obj M)) ∧
        let P := ∏ᶜ fun n : ℕ => E.obj (Opposite.op n)
        let d : P ⟶ P := Pi.lift fun n : ℕ =>
          Pi.π (fun n : ℕ => E.obj (Opposite.op n)) n -
            Pi.π (fun n : ℕ => E.obj (Opposite.op n)) (n + 1) ≫
              E.map (homOfLE (Nat.le_succ n)).op
        ∃ (a : K ⟶ P) (b : P ⟶ K⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk a d b ∈ distTriang (DerivedCategory Ab.{0}) ∧
          ∀ p : ℤ,
            let H : ℤ → Rlim.InvSystemAb := fun q =>
              E ⋙ DerivedCategory.homologyFunctor Ab.{0} q
            let HP : ℤ → Ab.{0} := fun q =>
              (DerivedCategory.homologyFunctor Ab.{0} q).obj P
            let PH : ℤ → Ab.{0} := fun q =>
              ∏ᶜ fun n : ℕ => (H q).obj (Opposite.op n)
            let δH : (q : ℤ) → (PH q ⟶ PH q) := fun q => Rlim.delta (H q)
            let R1lim := Rlim.firstDerivedLimit (H (p - 1))
            let HpK := (DerivedCategory.homologyFunctor Ab.{0} p).obj K
            let limHp := lim.obj (H p)
            let T := Pretriangulated.Triangle.mk a d b
            let connecting : HP (p - 1) ⟶ HpK :=
              (DerivedCategory.homologyFunctor Ab.{0} 0).homologySequenceδ
                T (p - 1) p (by omega)
            ∃ (ePrev : HP (p - 1) ≅ PH (p - 1)) (eCurr : HP p ≅ PH p),
              (∀ n : ℕ, ePrev.hom ≫ Pi.π
                  (fun n : ℕ => (H (p - 1)).obj (Opposite.op n)) n =
                (DerivedCategory.homologyFunctor Ab.{0} (p - 1)).map
                  (Pi.π (fun n : ℕ => E.obj (Opposite.op n)) n)) ∧
              (∀ n : ℕ, eCurr.hom ≫ Pi.π
                  (fun n : ℕ => (H p).obj (Opposite.op n)) n =
                (DerivedCategory.homologyFunctor Ab.{0} p).map
                  (Pi.π (fun n : ℕ => E.obj (Opposite.op n)) n)) ∧
              (DerivedCategory.homologyFunctor Ab.{0} (p - 1)).map d ≫ ePrev.hom =
                ePrev.hom ≫ δH (p - 1) ∧
              (DerivedCategory.homologyFunctor Ab.{0} p).map d ≫ eCurr.hom =
                eCurr.hom ≫ δH p ∧
              ∃ (eLim : limHp ≅ kernel (δH p))
                (hConnecting : δH (p - 1) ≫ ePrev.inv ≫ connecting = 0)
                (hKernel : (DerivedCategory.homologyFunctor Ab.{0} p).map a ≫
                  eCurr.hom ≫ δH p = 0),
                (∀ n : ℕ, eLim.hom ≫ kernel.ι (δH p) ≫
                    Pi.π (fun n : ℕ => (H p).obj (Opposite.op n)) n =
                  limit.π (H p) (Opposite.op n)) ∧
                let i : R1lim ⟶ HpK :=
                  cokernel.desc (δH (p - 1)) (ePrev.inv ≫ connecting) hConnecting
                let q : HpK ⟶ limHp :=
                  kernel.lift (δH p)
                    ((DerivedCategory.homologyFunctor Ab.{0} p).map a ≫ eCurr.hom)
                    hKernel ≫ eLim.inv
                ∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨RF, α, hRF, hRF_lim⟩ := Rlim.lim_hasRightDerivedFunctor_and_isDerivedLimit
  refine ⟨RF, α, hRF, Pretriangulated.exists_isDerivedLimit E,
    Stacks.InverseSystem.AbelianGroupDerivedLift.exists_lift_of_inverseSystem E, ?_⟩
  intro K hK
  constructor
  · intro M ψ hψ
    let e : Rlim.derivedEvaluationSystem M ≅ E :=
      NatIso.ofComponents ψ (fun f => hψ f)
    obtain ⟨hP, hM⟩ := hRF_lim M
    let := hP
    exact derivedLimit_iso E K (RF.obj M) hK
      (isDerivedLimit_of_iso E (Rlim.derivedEvaluationSystem M) e (RF.obj M) hM)
  · obtain ⟨a, b, hT, hs⟩ := DerivedCategory.isDerivedLimit_homology_shortExact E K hK
    refine ⟨a, b, hT, ?_⟩
    intro p
    let H := DerivedCategory.homologyFunctor Ab.{0} p
    let H₁ := DerivedCategory.homologyFunctor Ab.{0} (p - 1)
    let X : ℕ → DerivedCategory Ab.{0} := fun n => E.obj (Opposite.op n)
    have hseq := hs p
    dsimp only at hseq
    rw [← Rlim.delta_eq_lift (E ⋙ H₁)] at hseq
    obtain ⟨ePrev, i₀, q₀, w₀, hePrev, hi₀, hq₀, hshort⟩ := hseq
    have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X p
    let eCurr : H.obj (∏ᶜ X) ≅ ∏ᶜ fun n => H.obj (X n) :=
      asIso (piComparison H X)
    have hePrevπ (n : ℕ) : ePrev.hom ≫ Pi.π (fun n => H₁.obj (X n)) n =
        H₁.map (Pi.π X n) := by
      rw [hePrev]
      exact piComparison_comp_π H₁ X n
    have heCurr (n : ℕ) : eCurr.hom ≫ Pi.π (fun n => H.obj (X n)) n =
        H.map (Pi.π X n) := by simp [eCurr]
    have hdPrev : H₁.map (Pi.lift fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
        E.map (homOfLE (Nat.le_succ n)).op) ≫ ePrev.hom =
        ePrev.hom ≫ Rlim.delta (E ⋙ H₁) := by
      rw [hePrev]
      rw [CochainComplex.map_pi_lift_sub_comp_piComparison H₁ X
        (fun n => E.map (homOfLE (Nat.le_succ n)).op)]
      rw [Rlim.delta_eq_lift]
      rfl
    have hdCurr : H.map (Pi.lift fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
        E.map (homOfLE (Nat.le_succ n)).op) ≫ eCurr.hom =
        eCurr.hom ≫ Rlim.delta (E ⋙ H) := by
      change H.map (Pi.lift fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
          E.map (homOfLE (Nat.le_succ n)).op) ≫ piComparison H X =
        piComparison H X ≫ Rlim.delta (E ⋙ H)
      rw [CochainComplex.map_pi_lift_sub_comp_piComparison H X
        (fun n => E.map (homOfLE (Nat.le_succ n)).op)]
      rw [Rlim.delta_eq_lift]
      rfl
    refine ⟨ePrev, eCurr, hePrevπ, heCurr, hdPrev, hdCurr, ?_⟩
    let δ := Rlim.delta (E ⋙ H)
    let δPrev := Rlim.delta (E ⋙ H₁)
    let dK : (∏ᶜ fun n : ℕ => E.obj (Opposite.op n)) ⟶
        ∏ᶜ fun n : ℕ => E.obj (Opposite.op n) := Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => E.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ => E.obj (Opposite.op n)) (n + 1) ≫
          E.map (homOfLE (Nat.le_succ n)).op
    obtain ⟨eLim, heLimπ⟩ := Rlim.limit_kernel_iso (E ⋙ H)
    change cokernel.π δPrev ≫ i₀ = ePrev.inv ≫
      (DerivedCategory.homologyFunctor Ab.{0} 0).homologySequenceδ
        (Pretriangulated.Triangle.mk a dK b) (p - 1) p (by omega) at hi₀
    have hc : δPrev ≫ ePrev.inv ≫
        (DerivedCategory.homologyFunctor Ab.{0} 0).homologySequenceδ
          (Pretriangulated.Triangle.mk a dK b) (p - 1) p (by omega) = 0 := by
      rw [← hi₀, ← Category.assoc, cokernel.condition, zero_comp]
    have hk : H.map a ≫ eCurr.hom ≫ δ = 0 := by
      rw [← hdCurr, ← Category.assoc, ← H.map_comp]
      have had : a ≫ dK = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
      rw [had, H.map_zero, zero_comp]
    refine ⟨eLim, hc, hk, heLimπ, ?_⟩
    · let i := cokernel.desc δPrev
          (ePrev.inv ≫ (DerivedCategory.homologyFunctor Ab.{0} 0).homologySequenceδ
            (Pretriangulated.Triangle.mk a dK b) (p - 1) p (by omega)) hc
      let q := kernel.lift δ (H.map a ≫ eCurr.hom) hk ≫ eLim.inv
      have hi : i = i₀ := by
        rw [← cancel_epi (cokernel.π δPrev)]
        dsimp only [i]
        rw [cokernel.π_desc]
        exact hi₀.symm
      have hq : q = q₀ := by
        apply limit.hom_ext
        intro n
        rw [hq₀]
        dsimp only [q]
        rw [← heLimπ n.unop, Category.assoc, Iso.inv_hom_id_assoc, kernel.lift_ι_assoc,
          Category.assoc]
        exact congrArg (fun f => H.map a ≫ f) (heCurr n.unop)
      change ∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact
      simpa only [hi, hq] using (show ∃ w : i₀ ≫ q₀ = 0,
        (ShortComplex.mk i₀ q₀ w).ShortExact from ⟨w₀, hshort⟩)

end Rlim

end

end
