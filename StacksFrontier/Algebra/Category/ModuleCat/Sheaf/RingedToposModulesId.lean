module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardCompMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId

/-!
# The identity morphism of a ringed topos, and its direct image of sheaves of modules

The identity morphism of a ringed topos `(Sh(C), O)` is a morphism of ringed topoi
`Stacks.Sheaves.RingedToposModules.RingedToposHom.id`, whose underlying morphism of topoi is the
identity and whose structure map is the identity on underlying sheaves of sets. The direct image
of sheaves of modules along it is the identity functor, as a **monoidal** natural isomorphism for
the lax monoidal structure of the direct image (the right adjoint of the monoidal pullback of
Tag 03EL) and the identity lax monoidal structure of `𝟭`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.RingedToposHom.id`: the identity morphism of a ringed topos.
* `Stacks.Sheaves.RingedToposModules.pushforwardModulesIdIso`: `id_* ≅ 𝟭` on sheaves of modules,
  the identity on underlying sheaves of sets.

## Main results

* `Stacks.Sheaves.RingedToposModules.isMonoidal_pushforwardModulesIdIso_hom`: the comparison
  `id_* ≅ 𝟭` is a monoidal natural transformation.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf

universe w v u

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace Stacks.Sheaves.RingedToposModules

section Identity

variable (X : RingedTopos.{v, u, w})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]

/-- **The identity morphism of a ringed topos**: the identity morphism of the underlying topos,
with structure map the identity on underlying sheaves of sets. It is the reading
`AlgebraicGeometry.RingedToposHom.toModulesHom` of the identity morphism
`AlgebraicGeometry.RingedToposHom.id` of Stacks 01D3. -/
protected def RingedToposHom.id : RingedToposHom X X :=
  (AlgebraicGeometry.RingedToposHom.id X).toModulesHom

/-- The direct image of the identity morphism of a ringed topos is the identity functor. -/
@[simp]
theorem RingedToposHom.id_toToposHom_pushforward :
    (RingedToposHom.id X).toToposHom.pushforward = 𝟭 X.Topos :=
  rfl

/-- The inverse image of the identity morphism of a ringed topos is the identity functor. -/
@[simp]
theorem RingedToposHom.id_toToposHom_inverseImage :
    (RingedToposHom.id X).toToposHom.inverseImage = 𝟭 X.Topos :=
  rfl

/-- The structure map of the identity morphism of a ringed topos is the identity on underlying
sheaves of sets. -/
theorem fSharpSet_id : fSharpSet (RingedToposHom.id X) = 𝟙 _ :=
  rfl

end Identity

section Comparison

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : RingedToposHom X X)
  (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A comparison `σ : f_* ⟶ 𝟭` of the geometric direct image with the identity, read as a morphism
from the underlying sheaf of sets of `f_*M` to that of `M`. -/
abbrev pushforwardIdComparisonSheafHom (σ : f.toToposHom.pushforward ⟶ 𝟭 X.Topos) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((pushforwardModules f).obj M) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M :=
  σ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)

/-- A comparison `σ : 𝟭 ⟶ f_*`, read as a morphism from the underlying sheaf of sets of `M` to
that of `f_*M`. -/
abbrev pushforwardIdComparisonSheafHomSymm (σ : 𝟭 X.Topos ⟶ f.toToposHom.pushforward) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((pushforwardModules f).obj M) :=
  σ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)

/-- A comparison `f_* ⟶ 𝟭` of geometric direct images is additive on sections. -/
lemma sectionsFunctor_map_pushforwardIdComparison_add (V : X.Cᵒᵖ)
    (σ : f.toToposHom.pushforward ⟶ 𝟭 X.Topos)
    (x y : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((pushforwardModules f).obj M))) :
    (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHom f M σ) (x + y) =
      (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHom f M σ) x +
        (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHom f M σ) y := by
  have hnat := Sheaf.moduleAddObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
    (Functor.whiskerRight σ (Sheaf.sectionsFunctor X.J V)) x y
  rw [pushforwardModules_add f M V x y]
  exact hnat.trans (Sheaf.sectionsFunctor_map_moduleAddHom
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G := M) V _ _)

/-- A comparison `f_* ⟶ 𝟭` of geometric direct images which carries the structure map of `f` to
the identity is linear on sections. -/
lemma sectionsFunctor_map_pushforwardIdComparison_smul (V : X.Cᵒᵖ)
    (σ : f.toToposHom.pushforward ⟶ 𝟭 X.Topos)
    (hσ : fSharpSet f ≫ σ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      𝟙 _)
    (r : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((pushforwardModules f).obj M))) :
    (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHom f M σ) (r • x) =
      r • (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHom f M σ) x := by
  have hnat := Sheaf.moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
    (Functor.whiskerRight σ (Sheaf.sectionsFunctor X.J V))
    ((Sheaf.sectionsFunctor X.J V).map (fSharpSet f) r) x
  have hscal : (Sheaf.sectionsFunctor X.J V).map
        (σ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        ((Sheaf.sectionsFunctor X.J V).map (fSharpSet f) r) = r :=
    ((Sheaf.sectionsFunctor X.J V).map_comp_apply (fSharpSet f)
        (σ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) r).symm.trans
      ((congrArg (fun m ↦ (Sheaf.sectionsFunctor X.J V).map m r) hσ).trans
        ((Sheaf.sectionsFunctor X.J V).map_id_apply _ r))
  rw [pushforwardModules_smul_fSharpSet f M V r x]
  refine hnat.trans ?_
  rw [Functor.whiskerRight_app, hscal]
  exact Sheaf.sectionsFunctor_map_moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G := M) V _ _

/-- A comparison `𝟭 ⟶ f_*` of geometric direct images is additive on sections. -/
lemma sectionsFunctor_map_pushforwardIdComparisonSymm_add (V : X.Cᵒᵖ)
    (σ : 𝟭 X.Topos ⟶ f.toToposHom.pushforward)
    (x y : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :
    (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ) (x + y) =
      (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ) x +
        (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ) y := by
  have hnat := Sheaf.moduleAddObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
    (Functor.whiskerRight σ (Sheaf.sectionsFunctor X.J V)) x y
  rw [pushforwardModules_add f M V]
  exact (congrArg ((Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ))
    (Sheaf.sectionsFunctor_map_moduleAddHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G := M) V x y).symm).trans hnat

/-- A comparison `𝟭 ⟶ f_*` of geometric direct images which carries the identity to the structure
map of `f` is linear on sections. -/
lemma sectionsFunctor_map_pushforwardIdComparisonSymm_smul (V : X.Cᵒᵖ)
    (σ : 𝟭 X.Topos ⟶ f.toToposHom.pushforward)
    (hσ : σ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet f)
    (r : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :
    (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ) (r • x) =
      r • (Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ) x := by
  have hnat := Sheaf.moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M
    (Functor.whiskerRight σ (Sheaf.sectionsFunctor X.J V)) r x
  rw [pushforwardModules_smul_fSharpSet f M V, ← hσ]
  exact (congrArg ((Sheaf.sectionsFunctor X.J V).map (pushforwardIdComparisonSheafHomSymm f M σ))
    (Sheaf.sectionsFunctor_map_moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G := M) V r x).symm).trans hnat

variable (τ : f.toToposHom.pushforward ≅ 𝟭 X.Topos)
  (hτ : fSharpSet f ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = 𝟙 _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
include hτ in
/-- The inverse of the comparison carries the identity to the structure map. -/
theorem inv_app_ringSheaf_eq_fSharpSet :
    τ.inv.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet f :=
  ((Iso.comp_hom_eq_id
    (τ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).1 hτ).symm

/-- The comparison `f_*M ≅ M` of sheaves of modules attached to a comparison `τ : f_* ≅ 𝟭` of the
geometric direct image with the identity carrying the structure map of `f` to the identity. -/
def pushforwardModulesIsoOfComparisonApp :
    (pushforwardModules f).obj M ≅ M where
  hom := ofSheafHom (pushforwardIdComparisonSheafHom f M τ.hom)
    (fun V ↦ sectionsFunctor_map_pushforwardIdComparison_add f M V τ.hom)
    (fun V ↦ sectionsFunctor_map_pushforwardIdComparison_smul f M V τ.hom hτ)
  inv := ofSheafHom (pushforwardIdComparisonSheafHomSymm f M τ.inv)
    (fun V ↦ sectionsFunctor_map_pushforwardIdComparisonSymm_add f M V τ.inv)
    (fun V ↦ sectionsFunctor_map_pushforwardIdComparisonSymm_smul f M V τ.inv
      (inv_app_ringSheaf_eq_fSharpSet f τ hτ))
  hom_inv_id := hom_ext_moduleSheafFunctor (by
    rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_ofSheafHom,
      moduleSheafFunctor_map_ofSheafHom, CategoryTheory.Functor.map_id]
    exact τ.hom_inv_id_app _)
  inv_hom_id := hom_ext_moduleSheafFunctor (by
    rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_ofSheafHom,
      moduleSheafFunctor_map_ofSheafHom, CategoryTheory.Functor.map_id]
    exact τ.inv_hom_id_app _)

/-- The comparison `f_*M ≅ M` is `τ` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesIsoOfComparisonApp_hom :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        (pushforwardModulesIsoOfComparisonApp f M τ hτ).hom =
      pushforwardIdComparisonSheafHom f M τ.hom :=
  rfl

variable {M}

/-- **A direct image of sheaves of modules isomorphic to the identity**: a comparison
`τ : f_* ≅ 𝟭` of the geometric direct image of `f : X ⟶ X` with the identity, carrying the
structure map of `f` to the identity, induces `f_* ≅ 𝟭` on sheaves of modules, which is `τ` on
underlying sheaves of sets. -/
def pushforwardModulesIsoOfComparison :
    pushforwardModules f ≅
      𝟭 (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  NatIso.ofComponents (fun M ↦ pushforwardModulesIsoOfComparisonApp f M τ hτ)
    (fun {M N} α ↦ hom_ext_moduleSheafFunctor (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      exact (congrArg (· ≫ _) (moduleSheafFunctor_map_pushforwardModules_map f α)).trans
        (τ.hom.naturality
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map α))))

/-- The comparison `f_* ≅ 𝟭` is `τ` on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesIsoOfComparison_hom_app
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        ((pushforwardModulesIsoOfComparison f τ hτ).hom.app M) =
      pushforwardIdComparisonSheafHom f M τ.hom :=
  rfl

end Comparison

section Generic

variable {C : Type*} [Category C]

/-- A composite of three morphisms followed by a fourth, from an equation for the first three. -/
theorem comp_comp_comp_of_eq {P Q R S T : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {e : P ⟶ S}
    (h : a ≫ b ≫ c = e) (d : S ⟶ T) : a ≫ b ≫ c ≫ d = e ≫ d := by
  rw [← h]
  simp only [Category.assoc]

end Generic

section Monoidal

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X X) (τ : f.toToposHom.pushforward ≅ 𝟭 X.Topos)
  (hτ : fSharpSet f ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = 𝟙 _)

/-- The tensorator followed by the comparison, on the canonical pairing read through the product
comparison: `τ` followed by the canonical pairing. -/
theorem prodComparison_comp_tensorPairing_comp_μ_comp_pushforwardModulesIsoOfComparison
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    prodComparison f.toToposHom.pushforward
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
      tensorPairing ((pushforwardModules f).obj M) ((pushforwardModules f).obj N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (Functor.LaxMonoidal.μ (pushforwardModules f) M N ≫
            (pushforwardModulesIsoOfComparison f τ hτ).hom.app (M ⊗ N)) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
        tensorPairing M N := by
  rw [CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_pushforwardModulesIsoOfComparison_hom_app]
  exact (comp_comp_comp_of_eq (prodComparison_comp_tensorPairing_comp_μ f M N) _).trans
    (τ.hom.naturality (tensorPairing M N))

/-- The tensor product of the two comparisons, on the canonical pairing read through the product
comparison: `τ` followed by the canonical pairing. -/
theorem prodComparison_comp_tensorPairing_comp_pushforwardModulesIsoOfComparison_tensorHom
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    prodComparison f.toToposHom.pushforward
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
      tensorPairing ((pushforwardModules f).obj M) ((pushforwardModules f).obj N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          ((pushforwardModulesIsoOfComparison f τ hτ).hom.app M ⊗ₘ
            (pushforwardModulesIsoOfComparison f τ hτ).hom.app N) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
        tensorPairing M N := by
  have h₂ := tensorPairing_comp_tensorHom ((pushforwardModulesIsoOfComparison f τ hτ).hom.app M)
    ((pushforwardModulesIsoOfComparison f τ hτ).hom.app N)
  exact (congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ tensorPairing M N) ((prodComparison_natural_of_natTrans τ.hom).symm.trans
      ((congrArg (_ ≫ ·) (prod.lift_fst_snd)).trans (Category.comp_id _)))))

/-- **The comparison `f_* ≅ 𝟭` is compatible with the tensorators.** -/
theorem pushforwardModulesIsoOfComparison_μ
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Functor.LaxMonoidal.μ (pushforwardModules f) M N ≫
        (pushforwardModulesIsoOfComparison f τ hτ).hom.app (M ⊗ N) =
      (pushforwardModulesIsoOfComparison f τ hτ).hom.app M ⊗ₘ
        (pushforwardModulesIsoOfComparison f τ hτ).hom.app N := by
  have := f.toToposHom.adj.rightAdjoint_preservesLimits
  refine hom_ext_tensorPairing ((cancel_epi (prodComparison f.toToposHom.pushforward
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))).1 ?_)
  exact (prodComparison_comp_tensorPairing_comp_μ_comp_pushforwardModulesIsoOfComparison f τ hτ
    M N).trans
      (prodComparison_comp_tensorPairing_comp_pushforwardModulesIsoOfComparison_tensorHom f τ hτ
        M N).symm

/-- **The comparison `f_* ≅ 𝟭` is compatible with the units**: on underlying sheaves of sets the
unit of the direct image is the structure map, which `τ` carries to the identity. -/
theorem pushforwardModulesIsoOfComparison_ε :
    Functor.LaxMonoidal.ε (pushforwardModules f) ≫
        (pushforwardModulesIsoOfComparison f τ hτ).hom.app
          (𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) = 𝟙 _ := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_ε,
    moduleSheafFunctor_map_pushforwardModulesIsoOfComparison_hom_app,
    CategoryTheory.Functor.map_id]
  exact hτ

/-- **The comparison `f_* ≅ 𝟭` of direct images of sheaves of modules is a monoidal natural
transformation**, for the lax monoidal structure of the direct image (the right adjoint of the
monoidal pullback of Tag 03EL) and the identity lax monoidal structure of `𝟭`. -/
instance isMonoidal_pushforwardModulesIsoOfComparison_hom :
    NatTrans.IsMonoidal (pushforwardModulesIsoOfComparison f τ hτ).hom where
  unit := (pushforwardModulesIsoOfComparison_ε f τ hτ).trans (Category.id_comp _).symm
  tensor M N := (pushforwardModulesIsoOfComparison_μ f τ hτ M N).trans (Category.comp_id _).symm

end Monoidal

/-! ### The identity morphism -/

section IdentityPushforward

variable (X : RingedTopos.{v, u, w})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The geometric direct image of the identity morphism is the identity functor. -/
abbrev idToposPushforwardIso : (RingedToposHom.id X).toToposHom.pushforward ≅ 𝟭 X.Topos :=
  Iso.refl _

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The identification of the geometric direct image of the identity with the identity carries
the structure map to the identity. -/
theorem fSharpSet_id_comp_idToposPushforwardIso :
    fSharpSet (RingedToposHom.id X) ≫
        (idToposPushforwardIso X).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = 𝟙 _ :=
  Category.comp_id _

/-- **The direct image of sheaves of modules along the identity morphism of a ringed topos is the
identity functor**: the comparison is the identity on underlying sheaves of sets. -/
def pushforwardModulesIdIso :
    pushforwardModules (RingedToposHom.id X) ≅
      𝟭 (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  pushforwardModulesIsoOfComparison (RingedToposHom.id X) (idToposPushforwardIso X)
    (fSharpSet_id_comp_idToposPushforwardIso X)

/-- The comparison `id_* ≅ 𝟭` is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesIdIso_hom_app
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        ((pushforwardModulesIdIso X).hom.app M) =
      pushforwardIdComparisonSheafHom (RingedToposHom.id X) M (idToposPushforwardIso X).hom :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The comparison `id_* ≅ 𝟭` is a monoidal natural transformation.** -/
instance isMonoidal_pushforwardModulesIdIso_hom :
    NatTrans.IsMonoidal (pushforwardModulesIdIso X).hom :=
  isMonoidal_pushforwardModulesIsoOfComparison_hom _ _ _

end IdentityPushforward

end Stacks.Sheaves.RingedToposModules

end
