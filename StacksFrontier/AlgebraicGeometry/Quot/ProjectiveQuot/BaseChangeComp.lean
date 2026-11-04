module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChange

/-!
# Base change of quotients of `𝒪^{⊕ r}` on `ℙⁿ_T` is compatible with composition

For `h : T'' ⟶ T'` and `g : T' ⟶ T`, pulling a submodule `K ⊆ 𝒪^{⊕ r}` of `ℙⁿ_T` back along
`g` and then along `h` gives its pullback along `h ≫ g`. This is the composition half of the
functoriality of `T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` (Stacks 09TR, 0DNF).

## Main results

* `AlgebraicGeometry.ProjectiveQuot.freeModulePullbackIso_inv_comp`: the identifications
  `g^* 𝒪^{⊕ r} ≅ 𝒪^{⊕ r}` are compatible with composition, from the corresponding statement
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` for the structure sheaf.
* `AlgebraicGeometry.ProjectiveQuot.baseChange_comp`: `(h ≫ g)^* K = h^*(g^* K)`.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

/-- On the `j`-th summand, the identification `𝒪^{⊕ r} ≅ g^* 𝒪^{⊕ r}` is the inverse of the
identification `g^* 𝒪 ≅ 𝒪` followed by the pullback of the `j`-th inclusion. -/
@[reassoc]
theorem ι_freeModulePullbackIso_inv {T' T : Scheme.{u}} (g : T' ⟶ T) (j : Fin r) :
    (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T')) j :
        _ ⟶ freeModule n r T') ≫ (freeModulePullbackIso n r g).inv =
      (Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)).inv ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
          (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j :
            _ ⟶ freeModule n r T) := by
  simp only [freeModulePullbackIso, Iso.trans_inv, Sigma.ι_mapIso_inv_assoc,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

/-- The inverse form of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`: the
identifications `f^* 𝒪 ≅ 𝒪` are compatible with composition. -/
@[reassoc]
theorem pullbackUnitIso_inv_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (w : f ≫ g = k) :
    (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullbackComp f g).hom.app (Scheme.unitModule Z) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Scheme.unitModule Z) =
      (Scheme.Modules.pullbackUnitIso k).inv := by
  rw [← cancel_mono (Scheme.Modules.pullbackUnitIso k).hom, Iso.inv_hom_id,
    ← Scheme.Modules.pullbackUnitIso_comp_eq f g k w]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

/-- **The identifications `g^* 𝒪^{⊕ r} ≅ 𝒪^{⊕ r}` are compatible with composition.** -/
theorem freeModulePullbackIso_inv_comp {T'' T' T : Scheme.{u}} (h : T'' ⟶ T') (g : T' ⟶ T) :
    (freeModulePullbackIso n r h).inv ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n h)).map
          (freeModulePullbackIso n r g).inv ≫
        (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
          (projectiveSpaceOverMap n g)).hom.app (freeModule n r T) ≫
        (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.app
          (freeModule n r T) =
      (freeModulePullbackIso n r (h ≫ g)).inv := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [ι_freeModulePullbackIso_inv_assoc (n := n) (r := r) h j, ← Functor.map_comp_assoc,
    ι_freeModulePullbackIso_inv (n := n) (r := r) g j,
    ι_freeModulePullbackIso_inv (n := n) (r := r) (h ≫ g) j, Functor.map_comp_assoc]
  have nat₁ := (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
    (projectiveSpaceOverMap n g)).hom.naturality
      (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j)
  have nat₂ :
      (Scheme.Modules.pullback (projectiveSpaceOverMap n h ≫ projectiveSpaceOverMap n g)).map
        (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j :
          _ ⟶ freeModule n r T) ≫
        (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.app
          (freeModule n r T) =
      (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.app _ ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n (h ≫ g))).map
          (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j :
            _ ⟶ freeModule n r T) :=
    (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.naturality _
  simp only [Functor.comp_map] at nat₁
  rw [reassoc_of% nat₁, nat₂,
    pullbackUnitIso_inv_comp_assoc _ _ _ (projectiveSpaceOverMap_comp n h g)]

/-- The kernel of a morphism followed by an isomorphism is the kernel of the morphism. -/
private theorem kernelSubobject_comp_iso {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z) [HasKernel f] [HasKernel (f ≫ e.hom)] :
    kernelSubobject (f ≫ e.hom) = kernelSubobject f :=
  kernelSubobject_comp_mono f e.hom

/-- **Base change is compatible with composition**: `(h ≫ g)^* K = h^*(g^* K)`. -/
theorem baseChange_comp {T'' T' T : Scheme.{u}} (h : T'' ⟶ T') (g : T' ⟶ T)
    (K : Subobject (freeModule n r T)) :
    baseChange (h ≫ g) K = baseChange h (baseChange g K) := by
  have nat₁ := (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
    (projectiveSpaceOverMap n g)).hom.naturality (quotientπ K)
  have nat₂ := (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.naturality
    (quotientπ K)
  simp only [Functor.comp_map] at nat₁
  let X := (Scheme.Modules.pullback (projectiveSpaceOverMap n h)).mapIso
      (quotientBaseChangeIso g K) ≪≫
    (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
        (projectiveSpaceOverMap n g)).app (quotient K) ≪≫
      (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).app (quotient K)
  have e : baseChangeQuotientMap h (baseChange g K) ≫ X.hom = baseChangeQuotientMap (h ≫ g) K := by
    simp only [X, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [baseChangeQuotientMap, Category.assoc]
    rw [← Functor.map_comp_assoc, quotientπ_quotientBaseChangeIso_hom, baseChangeQuotientMap,
      Functor.map_comp_assoc, reassoc_of% nat₁, nat₂, ← freeModulePullbackIso_inv_comp h g]
    simp only [Category.assoc]
  unfold baseChange
  calc kernelSubobject (baseChangeQuotientMap (h ≫ g) K)
      = kernelSubobject (baseChangeQuotientMap h (kernelSubobject (baseChangeQuotientMap g K)) ≫
          X.hom) := by simp only [baseChange] at e; simp only [e]
    _ = _ := kernelSubobject_comp_iso _ X

end AlgebraicGeometry.ProjectiveQuot

end
