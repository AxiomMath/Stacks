module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChangeComp
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient

/-!
# The functor `T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` on schemes

Pulling back along the identity does not change a submodule `K ⊆ 𝒪^{⊕ r}` of `ℙⁿ_T`; together
with the composition law `AlgebraicGeometry.ProjectiveQuot.baseChange_comp` and the stability of
`AlgebraicGeometry.ProjectiveQuot.hilbertFamilies` under base change, this makes
`T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` a contravariant functor on schemes (Stacks 09TR, 0DNF), the
functor of which Stacks 0DPA is about.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_id`: along the identity, the identification
  `𝟙^* 𝒪 ≅ 𝒪` is the component of `AlgebraicGeometry.Scheme.Modules.pullbackId`.
* `AlgebraicGeometry.ProjectiveQuot.baseChange_id`: `𝟙^* K = K`.
* `AlgebraicGeometry.ProjectiveQuot.hilbertFunctor n r P`: the functor
  `T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)`, read on kernels.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Along the identity, the identification `𝟙^* 𝒪 ≅ 𝒪` is the component at the structure sheaf of
`AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
theorem Scheme.Modules.pullbackUnitIso_id (X : Scheme.{u}) :
    (Scheme.Modules.pullbackUnitIso (𝟙 X)).hom =
      (Scheme.Modules.pullbackId X).hom.app (Scheme.unitModule X) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [Scheme.Modules.pullbackUnitIso_homEquiv, Adjunction.homEquiv_unit, pullbackId_unit]
  ext U
  rfl

/-- For an endomorphism `h` equal to the identity, the identification `h^* 𝒪 ≅ 𝒪` followed by
the inverse of `h^* ≅ 𝟙^* ≅ 𝟭` is the identity. -/
@[reassoc]
theorem Scheme.Modules.pullbackUnitIso_inv_pullbackCongr_pullbackId {X : Scheme.{u}}
    (h : X ⟶ X) (w : h = 𝟙 X) :
    (Scheme.Modules.pullbackUnitIso h).inv ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Scheme.unitModule X) ≫
        (Scheme.Modules.pullbackId X).hom.app (Scheme.unitModule X) =
      𝟙 _ := by
  subst w
  rw [← Scheme.Modules.pullbackUnitIso_id]
  simp [Scheme.Modules.pullbackCongr]

namespace ProjectiveQuot

variable {n r : ℕ}

variable (n) in
/-- The identification `𝟙^* ≅ 𝟭` of the pullback along `ℙⁿ_T ⟶ ℙⁿ_T`, the base change of the
identity of `T`. -/
def pullbackProjectiveSpaceOverMapIdIso (T : Scheme.{u}) :
    Scheme.Modules.pullback (projectiveSpaceOverMap n (𝟙 T)) ≅ 𝟭 _ :=
  Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_id n T) ≪≫
    Scheme.Modules.pullbackId (projectiveSpaceOver n T)

/-- Naturality of the identification `𝟙^* ≅ 𝟭`, with the identity functor's action unfolded. -/
private theorem pullbackProjectiveSpaceOverMapIdIso_naturality (T : Scheme.{u})
    {A B : (projectiveSpaceOver n T).Modules} (f : A ⟶ B) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n (𝟙 T))).map f ≫
        (pullbackProjectiveSpaceOverMapIdIso n T).hom.app B =
      (pullbackProjectiveSpaceOverMapIdIso n T).hom.app A ≫ f :=
  (pullbackProjectiveSpaceOverMapIdIso n T).hom.naturality f

/-- Along the identity of `T`, the identification `𝒪^{⊕ r} ≅ 𝟙^* 𝒪^{⊕ r}` is the inverse of the
identification `𝟙^* ≅ 𝟭`. -/
theorem freeModulePullbackIso_inv_id (T : Scheme.{u}) :
    (freeModulePullbackIso n r (𝟙 T)).inv ≫
        (pullbackProjectiveSpaceOverMapIdIso n T).hom.app (freeModule n r T) =
      𝟙 _ := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [ι_freeModulePullbackIso_inv_assoc (n := n) (r := r) (𝟙 T) j]
  rw [pullbackProjectiveSpaceOverMapIdIso_naturality, Category.comp_id]
  simp only [pullbackProjectiveSpaceOverMapIdIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc]
  rw [Scheme.Modules.pullbackUnitIso_inv_pullbackCongr_pullbackId_assoc _
    (projectiveSpaceOverMap_id n T)]

/-- **Base change along the identity**: `𝟙^* K = K`. -/
theorem baseChange_id (T : Scheme.{u}) (K : Subobject (freeModule n r T)) :
    baseChange (𝟙 T) K = K := by
  have e : baseChangeQuotientMap (𝟙 T) K ≫
      (pullbackProjectiveSpaceOverMapIdIso n T).hom.app (quotient K) = quotientπ K := by
    rw [baseChangeQuotientMap, Category.assoc, pullbackProjectiveSpaceOverMapIdIso_naturality,
      ← Category.assoc, freeModulePullbackIso_inv_id, Category.id_comp]
  unfold baseChange
  rw [← kernelSubobject_eq_of_comp_mono _ _ _ e]
  exact kernelSubobject_cokernel_π K

variable (n r) in
/-- **The functor `T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)`**, read on kernels: its value at a scheme `T` is
`AlgebraicGeometry.ProjectiveQuot.hilbertFamilies n r P T`, and a morphism `g : T' ⟶ T` acts by
`AlgebraicGeometry.ProjectiveQuot.baseChange g`. -/
def hilbertFunctor (P : Polynomial ℚ) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := hilbertFamilies n r P T.unop
  map g := TypeCat.ofHom fun K =>
    ⟨baseChange g.unop K.1, baseChange_mem_hilbertFamilies g.unop K.2⟩
  map_id T := ConcreteCategory.hom_ext _ _ fun K => Subtype.ext (baseChange_id T.unop K.1)
  map_comp g h := ConcreteCategory.hom_ext _ _ fun K =>
    Subtype.ext (baseChange_comp h.unop g.unop K.1)

/-- The underlying subobject of the image of `K` under `(hilbertFunctor n r P).map g` is the
base change `baseChange g.unop K`. -/
theorem hilbertFunctor_map_coe (P : Polynomial ℚ) {T T' : Scheme.{u}ᵒᵖ} (g : T ⟶ T')
    (K : (hilbertFunctor n r P).obj T) :
    ((hilbertFunctor n r P).map g K).1 = baseChange g.unop K.1 :=
  rfl

end ProjectiveQuot

end AlgebraicGeometry

end
