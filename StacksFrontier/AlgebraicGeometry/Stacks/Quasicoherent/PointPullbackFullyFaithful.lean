module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismConstructionA
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageMultiplication
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation
public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone

/-!
# Isomorphisms of point pullbacks come from 2-arrows (Stacks 0GRP)

Let `𝒳` be an algebraic stack with affine diagonal and `x₁, x₂ : Spec B ⟶ 𝒳` two points. Every
isomorphism `t : x₁^* ≅ x₂^*` of the tensor functors `QCoh(𝒪_𝒳) ⥤ Mod_B` is induced by a 2-arrow
`x₁ ≅ x₂` (Stacks 0GRP).

The proof uses the chart `g = x₁ : Spec B ⟶ 𝒳`, which is affine. For the terminal arrows
`(x₀ᵢ, g x₀ᵢ ⟶ xᵢ)`, `xᵢ^*(g_*𝒪) = Γ(x₀ᵢ)`; the transport by `t⁻¹` on `g_*𝒪` is a ring map
`Γ(x₀₂) ⟶ Γ(x₀₁)` (`pointTransportRingHom`, by monoidality and the multiplication of `g_*𝒪`)
which is linear over the functions of `Spec B` (`pointTransportFun_mul_restrictGlobal`), hence
comes from an arrow `k : x₀₁ ⟶ x₀₂` of the stack of `Spec B` (`exists_schemeStack_hom_of_ringHom`).
Then `t⁻¹` is restriction along `k` on every direct image
(`pointPullbackQuasicoherentDirectImageAddEquiv_app_eq_map`, by generation of quasi-coherent
modules on an affine scheme by `𝒪`), and so restriction along `g(k) ≫ t₂` is restriction along
`t₁` after `t⁻¹` on every quasi-coherent module (`map_homFunctor_comp_terminal_apply`, through
the units `M ⟶ g_* g^* M`). Composing with the arrow `x₁ ⟶ x₀₁` given by the identity 2-arrow of
`x₁` gives the 2-arrow.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullbackTransportIso_eq`: the
  statement for points identified with `Spec R` by arbitrary isomorphisms.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_and_exists_iso_pointPullbackTransportIso_eq`:
  **Stacks 0GRP**, for points over possibly different structure morphisms `q₁, q₂`, which agree.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullbackTransportIso_eq_of_over`:
  **Stacks 0GRP** in the source's form.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry

/-- **A ring map into the functions of `X` from those of an affine scheme `Y` is a morphism
`X ⟶ Y`**: the composite `X ⟶ Spec Γ(X) ⟶ Spec Γ(Y) ≅ Y` has `θ` as its map on global
sections. -/
theorem Scheme.appTop_toSpecΓ_comp_Spec_map_comp_isoSpec_inv {X Y : Scheme.{u}} [IsAffine Y]
    (θ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) :
    (X.toSpecΓ ≫ Spec.map θ ≫ Y.isoSpec.inv).appTop = θ := by
  have h : (X.toSpecΓ ≫ Spec.map θ ≫ Y.isoSpec.inv) ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map θ := by
    rw [Category.assoc, Category.assoc, show Y.isoSpec.inv ≫ Y.toSpecΓ = 𝟙 _ from
      Y.isoSpec.inv_hom_id, Category.comp_id]
  have h2 : Y.toSpecΓ.appTop ≫ (X.toSpecΓ ≫ Spec.map θ ≫ Y.isoSpec.inv).appTop =
      (Spec.map θ).appTop ≫ X.toSpecΓ.appTop := congrArg Scheme.Hom.appTop h
  rw [Scheme.toSpecΓ_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality] at h2
  exact (cancel_epi _).1 h2

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

section Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} {g : 𝒰 ⟶ 𝒳} (hg : IsAffineHom B S hS g)
  {R : Type u} [CommRing R] {x₁ x₂ : 𝒳.val.val.obj}
  (e₁ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₁) ≅ Spec (CommRingCat.of R))
  (e₂ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₂) ≅ Spec (CommRingCat.of R))
  (τ : pointPullback B S hS 𝒳 x₂ e₂ ⟶ pointPullback B S hS 𝒳 x₁ e₁)
  {t₁ : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) x₁} (ht₁ : IsTerminal t₁)
  {t₂ : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) x₂} (ht₂ : IsTerminal t₂)

/-- The map `Γ(x₀₂, 𝒪_𝒰) ⟶ Γ(x₀₁, 𝒪_𝒰)` induced by a transformation `τ : x₂^* ⟶ x₁^*` on
`g_*𝒪_𝒰`, read through the sections at the terminal arrows `(x₀ᵢ, g x₀ᵢ ⟶ xᵢ)`. -/
def pointTransportFun (c : FibredSite.objRing B S hS 𝒰.val.val.p t₂.left) :
    FibredSite.objRing B S hS 𝒰.val.val.p t₁.left :=
  pointSectionsAddEquiv hg e₁ ht₁
    ((τ.app ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))).hom
      ((pointSectionsAddEquiv hg e₂ ht₂).symm c))

/-- The map `pointTransportFun` is additive. -/
theorem pointTransportFun_add (c c' : FibredSite.objRing B S hS 𝒰.val.val.p t₂.left) :
    pointTransportFun hg e₁ e₂ τ ht₁ ht₂ (c + c') =
      pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c + pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c' := by
  simp only [pointTransportFun, map_add]

/-- If `τ` is monoidal, the map `pointTransportFun` is multiplicative. -/
theorem pointTransportFun_mul [NatTrans.IsMonoidal τ]
    (c c' : FibredSite.objRing B S hS 𝒰.val.val.p t₂.left) :
    pointTransportFun hg e₁ e₂ τ ht₁ ht₂ (c * c') =
      pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c * pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c' := by
  unfold pointTransportFun
  rw [pointSectionsAddEquiv_symm_mul hg e₂ ht₂]
  have key : Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 x₂ e₂) ((affineQuasicoherentDirectImage
      B S hS g hg).obj (quasicoherentUnit 𝒰)) ((affineQuasicoherentDirectImage B S hS g hg).obj
          (quasicoherentUnit 𝒰)) ≫
      (pointPullback B S hS 𝒳 x₂ e₂).map (affineDirectImageMul hg) ≫ τ.app
          ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)) =
      (τ.app ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)) ⊗ₘ τ.app
          ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))) ≫
              Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 x₁ e₁)
                  ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))
                      ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)) ≫
        (pointPullback B S hS 𝒳 x₁ e₁).map (affineDirectImageMul hg) := by
    rw [τ.naturality, NatTrans.IsMonoidal.tensor_assoc]
  have h₂ := congrArg (fun φ => φ.hom ((pointSectionsAddEquiv hg e₂ ht₂).symm c ⊗ₜ
    (pointSectionsAddEquiv hg e₂ ht₂).symm c')) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h₂
  rw [h₂]
  exact pointSectionsAddEquiv_affineDirectImageMul hg e₁ ht₁ _ _

/-- For an isomorphism of point pullbacks, the transport on `g_*𝒪_𝒰` is surjective. -/
theorem pointTransportFun_surjective
    (t : pointPullback B S hS 𝒳 x₁ e₁ ≅ pointPullback B S hS 𝒳 x₂ e₂) :
    Function.Surjective (pointTransportFun hg e₁ e₂ t.inv ht₁ ht₂) := fun c =>
  ⟨pointSectionsAddEquiv hg e₂ ht₂ ((t.hom.app ((affineQuasicoherentDirectImage B S hS g hg).obj
      (quasicoherentUnit 𝒰))).hom ((pointSectionsAddEquiv hg e₁ ht₁).symm c)),
    by
      unfold pointTransportFun
      rw [AddEquiv.symm_apply_apply]
      have h := congrArg (fun φ => φ.hom ((pointSectionsAddEquiv hg e₁ ht₁).symm c))
        (t.hom_inv_id_app ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
          at h
      rw [h, AddEquiv.apply_symm_apply]⟩

/-- For an isomorphism of tensor functors, the transport on `g_*𝒪_𝒰` sends `1` to `1`. -/
theorem pointTransportFun_one (t : pointPullback B S hS 𝒳 x₁ e₁ ≅ pointPullback B S hS 𝒳 x₂ e₂)
    [NatTrans.IsMonoidal t.hom] : pointTransportFun hg e₁ e₂ t.inv ht₁ ht₂ 1 = 1 := by
  obtain ⟨c, hc⟩ := pointTransportFun_surjective hg e₁ e₂ ht₁ ht₂ t 1
  have h := pointTransportFun_mul hg e₁ e₂ t.inv ht₁ ht₂ 1 c
  rw [one_mul, hc, mul_one] at h
  exact h.symm

/-- **An isomorphism of tensor functors `t : x₁^* ≅ x₂^*` induces a ring isomorphism
`Γ(x₀₂, 𝒪_𝒰) ⟶ Γ(x₀₁, 𝒪_𝒰)`** between the functions on the fibre products `x₀ᵢ = xᵢ ×_𝒳 𝒰`:
the transport by `t⁻¹` on `g_*𝒪_𝒰`. -/
def pointTransportRingHom (t : pointPullback B S hS 𝒳 x₁ e₁ ≅ pointPullback B S hS 𝒳 x₂ e₂)
    [NatTrans.IsMonoidal t.hom] :
    FibredSite.objRing B S hS 𝒰.val.val.p t₂.left →+* FibredSite.objRing B S hS 𝒰.val.val.p
        t₁.left where
  toFun := pointTransportFun hg e₁ e₂ t.inv ht₁ ht₂
  map_one' := pointTransportFun_one hg e₁ e₂ ht₁ ht₂ t
  map_mul' := pointTransportFun_mul hg e₁ e₂ t.inv ht₁ ht₂
  map_zero' := by simp only [pointTransportFun, map_zero]
  map_add' := pointTransportFun_add hg e₁ e₂ t.inv ht₁ ht₂

/-- The identification `y^*(g_{QCoh,*}𝒪_𝒰) ≃ Γ(x₀, 𝒪_𝒰)` of
`pointPullbackQuasicoherentDirectImageAddEquiv` is `pointSectionsAddEquiv` after the
identification `g_{QCoh,*} = g_*` for `g` affine. -/
theorem pointPullbackQuasicoherentDirectImageAddEquiv_quasicoherentUnit {y : 𝒳.val.val.obj}
    (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) y} (ht : IsTerminal t)
    (z : (pointPullback B S hS 𝒳 y e).obj
      ((quasicoherentDirectImage B S hS g).obj (quasicoherentUnit 𝒰))) :
    (pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e ht (quasicoherentUnit 𝒰) z :
        FibredSite.objRing B S hS 𝒰.val.val.p t.left) =
      pointSectionsAddEquiv hg e ht (((pointPullback B S hS 𝒳 y e).map
        ((affineQuasicoherentDirectImageIso B S hS g hg).hom.app
          (quasicoherentUnit 𝒰))).hom z) := by
  change ((stackModuleDirectImageSectionsIsoOfIsTerminal B S hS g .fppf ht).hom.app
      (quasicoherentUnit 𝒰).obj).hom (((pointPullback B S hS 𝒳 y e).map
        ((affineQuasicoherentDirectImageIso B S hS g hg).hom.app (quasicoherentUnit 𝒰))).hom z) = _
  rw [stackModuleDirectImageSectionsIsoOfIsTerminal_fppf]
  exact (pointSectionsAddEquiv_apply hg e ht _).symm

section Generation

variable {u₀ : 𝒰.val.val.obj} (hu₀ : IsTerminal u₀)
  (hu₀a : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒰.val.val.p.obj u₀)))

include hu₀ hu₀a in
/-- **On an algebraic stack with a final object over an affine scheme, the sections of a
quasi-coherent module over an affine object are generated by the images of maps from `𝒪`**
(`iSup_range_unit_map_app_eq_top_of_isTerminal`, for the structure sheaf spelled
`quasicoherentUnit`). -/
theorem iSup_range_quasicoherentUnit_map_app_eq_top {x : 𝒰.val.val.obj}
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒰.val.val.p.obj x)))
    (N : quasicoherentModules B S hS 𝒰) :
    ⨆ h : quasicoherentUnit 𝒰 ⟶ N,
      (LinearMap.range (h.hom.val.app (op x)).hom).toAddSubgroup = ⊤ := by
  refine eq_top_iff.2 fun n _ => ?_
  have hn := iSup_range_unit_map_app_eq_top_of_isTerminal B S hS 𝒰 hu₀ hu₀a hx N ▸
    AddSubgroup.mem_top n
  refine AddSubgroup.iSup_induction _ (C := fun n => n ∈ ⨆ h : quasicoherentUnit 𝒰 ⟶ N,
    (LinearMap.range (h.hom.val.app (op x)).hom).toAddSubgroup) hn (fun h n hn => ?_)
    (zero_mem _) (fun _ _ => add_mem)
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hn
  exact AddSubgroup.mem_iSup_of_mem (ObjectProperty.homMk (X := quasicoherentUnit 𝒰) h.hom)
    ⟨c, rfl⟩

end Generation

section GlobalSections

variable {u₀ : 𝒰.val.val.obj} (hu₀ : IsTerminal u₀)

/-- The restriction of a function on the final object `u₀` of `𝒰` to an object `u`. -/
abbrev restrictGlobal (u : 𝒰.val.val.obj) (a : FibredSite.objRing B S hS 𝒰.val.val.p u₀) :
    FibredSite.objRing B S hS 𝒰.val.val.p u :=
  ((FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids
    .fppf).obj.map (hu₀.from u).op).hom a

/-- Multiplication by a global function `a`, an endomorphism of `𝒪_𝒰`. -/
def globalMulHom (a : FibredSite.objRing B S hS 𝒰.val.val.p u₀) :
    (quasicoherentUnit 𝒰).obj ⟶ (quasicoherentUnit 𝒰).obj :=
  (quasicoherentUnit 𝒰).obj.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun X => (quasicoherentUnit 𝒰).obj.val.map (hu₀.from X.unop).op a) (fun X Y k =>
      ((quasicoherentUnit 𝒰).obj.val.map_comp_apply (hu₀.from X.unop).op k a).symm.trans
        (congrArg (fun b : op u₀ ⟶ Y => ((quasicoherentUnit 𝒰).obj.val.map b).hom a)
          (show (hu₀.from X.unop).op ≫ k = (hu₀.from Y.unop).op from
            Quiver.Hom.unop_inj (hu₀.hom_ext _ _)))))

/-- On sections over `u`, `globalMulHom hu₀ a` is multiplication by the restriction of `a` to
`u`. -/
theorem globalMulHom_app (a : FibredSite.objRing B S hS 𝒰.val.val.p u₀) (u : 𝒰.val.val.obj)
    (c : FibredSite.objRing B S hS 𝒰.val.val.p u) :
    (((globalMulHom hu₀ a).val.app (op u)).hom c : FibredSite.objRing B S hS 𝒰.val.val.p u) =
      c * restrictGlobal hu₀ u a := by
  let 𝒪 := (FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids
    .fppf).obj
  have h1 : ((globalMulHom hu₀ a).val.app (op u)).hom (1 : 𝒪.obj (op u)) =
      restrictGlobal hu₀ u a :=
    ((quasicoherentUnit 𝒰).obj.unitHomEquiv_apply_coe _ (op u)).symm.trans
      (congrArg (fun s' : (quasicoherentUnit 𝒰).obj.val.sections => s'.val (op u))
        ((quasicoherentUnit 𝒰).obj.unitHomEquiv.apply_symm_apply _))
  have h2 := ((globalMulHom hu₀ a).val.app (op u)).hom.map_smul (show 𝒪.obj (op u) from c)
    (1 : 𝒪.obj (op u))
  exact (congrArg _ (mul_one (show 𝒪.obj (op u) from c)).symm).trans (h2.trans
    (congrArg (fun z => (show 𝒪.obj (op u) from c) • z) h1))

/-- **A transformation of point pullbacks is linear over the global functions of `𝒰`**: on
`g_*𝒪_𝒰` it commutes with multiplication by a global function `a` of `𝒰`. -/
theorem pointTransportFun_mul_restrictGlobal (a : FibredSite.objRing B S hS 𝒰.val.val.p u₀)
    (c : FibredSite.objRing B S hS 𝒰.val.val.p t₂.left) :
    pointTransportFun hg e₁ e₂ τ ht₁ ht₂ (c * restrictGlobal hu₀ t₂.left a) =
      pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c * restrictGlobal hu₀ t₁.left a := by
  let φG : ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)) ⟶
      ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)) :=
          ObjectProperty.homMk
    ((fppfModulesPushforward B S hS g).map (globalMulHom hu₀ a))
  have key₂ : (pointSectionsAddEquiv hg e₂ ht₂).symm (c * restrictGlobal hu₀ t₂.left a) =
      ((pointPullback B S hS 𝒳 x₂ e₂).map φG).hom ((pointSectionsAddEquiv hg e₂ ht₂).symm c) := by
    rw [AddEquiv.symm_apply_eq]
    refine Eq.trans ?_ (pointSectionsAddEquiv_map hg e₂ ht₂ (globalMulHom hu₀ a) _).symm
    rw [AddEquiv.apply_symm_apply]
    exact (globalMulHom_app hu₀ a t₂.left c).symm
  have nat : (τ.app ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))).hom
      (((pointPullback B S hS 𝒳 x₂ e₂).map φG).hom
      ((pointSectionsAddEquiv hg e₂ ht₂).symm c)) =
      ((pointPullback B S hS 𝒳 x₁ e₁).map φG).hom ((τ.app ((affineQuasicoherentDirectImage B S hS
          g hg).obj (quasicoherentUnit 𝒰))).hom
        ((pointSectionsAddEquiv hg e₂ ht₂).symm c)) :=
    NatTrans.naturality_apply τ φG _
  unfold pointTransportFun
  rw [key₂, nat]
  exact (pointSectionsAddEquiv_map hg e₁ ht₁ (globalMulHom hu₀ a) _).trans
    (globalMulHom_app hu₀ a t₁.left _)

end GlobalSections

/-- The identification `g_{QCoh,*}𝒪_𝒰 ≅ g_*𝒪_𝒰` read through the two sections identifications
at a terminal arrow. -/
theorem pointPullbackQuasicoherentDirectImageAddEquiv_symm_quasicoherentUnit {y : 𝒳.val.val.obj}
    (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) y} (ht : IsTerminal t)
    (c : (quasicoherentUnit 𝒰).obj.val.obj (op t.left)) :
    ((pointPullback B S hS 𝒳 y e).map
        ((affineQuasicoherentDirectImageIso B S hS g hg).hom.app (quasicoherentUnit 𝒰))).hom
      ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e ht (quasicoherentUnit 𝒰)).symm
          c) =
      (pointSectionsAddEquiv hg e ht).symm c :=
  (AddEquiv.eq_symm_apply _).2
    ((pointPullbackQuasicoherentDirectImageAddEquiv_quasicoherentUnit hg e ht _).symm.trans
      ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e ht (quasicoherentUnit
          𝒰)).apply_symm_apply c))

/-- `pointTransportFun`, read through `pointPullbackQuasicoherentDirectImageAddEquiv`. -/
theorem pointPullbackQuasicoherentDirectImageAddEquiv_transport
    (c : (quasicoherentUnit 𝒰).obj.val.obj (op t₂.left)) :
    pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₁ ht₁ (quasicoherentUnit 𝒰)
        ((τ.app ((quasicoherentDirectImage B S hS g).obj (quasicoherentUnit 𝒰))).hom
          ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂ (quasicoherentUnit
              𝒰)).symm c)) =
      (pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c : FibredSite.objRing B S hS 𝒰.val.val.p t₁.left) := by
  have hτA := NatTrans.naturality_apply τ
    ((affineQuasicoherentDirectImageIso B S hS g hg).hom.app (quasicoherentUnit 𝒰))
    ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂ (quasicoherentUnit 𝒰)).symm
        c)
  refine (pointPullbackQuasicoherentDirectImageAddEquiv_quasicoherentUnit hg e₁ ht₁ _).trans ?_
  rw [← hτA, pointPullbackQuasicoherentDirectImageAddEquiv_symm_quasicoherentUnit hg e₂ ht₂]
  rfl

section Arrow

variable {u₀ : 𝒰.val.val.obj} (hu₀ : IsTerminal u₀)
  (hu₀a : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒰.val.val.p.obj u₀)))
  (hx₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒰.val.val.p.obj t₂.left)))
  {k : t₁.left ⟶ t₂.left}
  (hk : ∀ c : (quasicoherentUnit 𝒰).obj.val.obj (op t₂.left),
    ((quasicoherentUnit 𝒰).obj.val.map k.op).hom c =
      (pointTransportFun hg e₁ e₂ τ ht₁ ht₂ c : FibredSite.objRing B S hS 𝒰.val.val.p t₁.left))

include hu₀ hu₀a hx₂ hk in
/-- **On every direct image, the transformation `τ : x₂^* ⟶ x₁^*` is restriction along `k`.**
If `τ` acts on `g_*𝒪_𝒰`, through the sections at the terminal arrows, as restriction of functions
along an arrow `k : x₀₁ ⟶ x₀₂` of `𝒰`, then it acts on `g_* N`, through
`x_i^*(g_* N) ≃ N(x₀ᵢ)`, as restriction along `k`, for every quasi-coherent `N` on `𝒰`: the
sections of `N` over `x₀₂` are generated by the images of maps `𝒪_𝒰 ⟶ N`. -/
theorem pointPullbackQuasicoherentDirectImageAddEquiv_app_eq_map
    (N : quasicoherentModules B S hS 𝒰)
    (z : (pointPullback B S hS 𝒳 x₂ e₂).obj ((quasicoherentDirectImage B S hS g).obj N)) :
    pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₁ ht₁ N
        ((τ.app ((quasicoherentDirectImage B S hS g).obj N)).hom z) =
      (N.obj.val.map k.op).hom (pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂ N
          z) := by
  obtain ⟨n, rfl⟩ := (pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂
      N).symm.surjective z
  rw [AddEquiv.apply_symm_apply]
  have hn : n ∈ ⨆ h : quasicoherentUnit 𝒰 ⟶ N,
      (LinearMap.range (h.hom.val.app (op t₂.left)).hom).toAddSubgroup :=
    (iSup_range_quasicoherentUnit_map_app_eq_top hu₀ hu₀a hx₂ N) ▸ AddSubgroup.mem_top n
  refine AddSubgroup.iSup_induction _ (C := fun n =>
    pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₁ ht₁ N
        ((τ.app ((quasicoherentDirectImage B S hS g).obj N)).hom
          ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂ N).symm n)) =
      (N.obj.val.map k.op).hom n) hn ?_ ?_ ?_
  · intro h n hn
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hn
    have hw : (pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂ N).symm
        ((h.hom.val.app (op t₂.left)).hom c) = ((pointPullback B S hS 𝒳 x₂ e₂).map
          ((quasicoherentDirectImage B S hS g).map h)).hom
              ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂
          (quasicoherentUnit 𝒰)).symm c) := by
      rw [AddEquiv.symm_apply_eq, pointPullbackQuasicoherentDirectImageAddEquiv_naturality,
        AddEquiv.apply_symm_apply]
    have hτ := NatTrans.naturality_apply τ ((quasicoherentDirectImage B S hS g).map h)
      ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂
        (quasicoherentUnit 𝒰)).symm c)
    rw [hw, hτ, pointPullbackQuasicoherentDirectImageAddEquiv_naturality]
    have key : pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₁ ht₁
        (quasicoherentUnit 𝒰)
        ((τ.app ((quasicoherentDirectImage B S hS g).obj (quasicoherentUnit 𝒰))).hom
          ((pointPullbackQuasicoherentDirectImageAddEquiv B S hS g hg e₂ ht₂
            (quasicoherentUnit 𝒰)).symm c)) = ((quasicoherentUnit 𝒰).obj.val.map k.op).hom c :=
      (pointPullbackQuasicoherentDirectImageAddEquiv_transport hg e₁ e₂ τ ht₁ ht₂ c).trans
        (hk c).symm
    exact (congrArg (h.hom.val.app (op t₁.left)).hom key).trans
      (PresheafOfModules.naturality_apply h.hom.val k.op c)
  · simp only [map_zero]
    rfl
  · intro n₁ n₂ h₁ h₂
    simp only [map_add, h₁, h₂]
    rfl

include hu₀ hu₀a hx₂ hk in
/-- **The transformation `τ : x₂^* ⟶ x₁^*` is restriction along the arrow `g(k) ≫ t₂`.**  Under
the hypotheses of `pointPullbackQuasicoherentDirectImageAddEquiv_app_eq_map`, for every
quasi-coherent module `M` on `𝒳` and `m ∈ M(x₂)`, restricting `m` along
`g(x₀₁) ⟶ g(x₀₂) ⟶ x₂` is restricting `τ(m)` along `g(x₀₁) ⟶ x₁`: compare the units
`M ⟶ g_* g^* M` at `x₁` and `x₂`. -/
theorem map_homFunctor_comp_terminal_apply (M : quasicoherentModules B S hS 𝒳)
    (m : (pointPullback B S hS 𝒳 x₂ e₂).obj M) :
    (M.obj.val.map ((CatFiberedInGroupoids.homFunctor g.hom).map k ≫ t₂.hom).op).hom m =
      (M.obj.val.map t₁.hom.op).hom ((τ.app M).hom m) := by
  have hu₁ := pointPullbackQuasicoherentDirectImageAddEquiv_unit B S hS g hg e₁ ht₁ M
    ((τ.app M).hom m)
  have hu₂ := pointPullbackQuasicoherentDirectImageAddEquiv_unit B S hS g hg e₂ ht₂ M m
  have hnat := NatTrans.naturality_apply τ (quasicoherentUnitOfIsAffineHom B S hS g hg M) m
  have hT := pointPullbackQuasicoherentDirectImageAddEquiv_app_eq_map hg e₁ e₂ τ ht₁ ht₂ hu₀ hu₀a
    hx₂ hk (quasicoherentPullbackObj B S hS g M)
    (((pointPullback B S hS 𝒳 x₂ e₂).map (quasicoherentUnitOfIsAffineHom B S hS g hg M)).hom m)
  rw [hnat, hu₂] at hT
  rw [← hu₁, hT, op_comp]
  exact M.obj.val.map_comp_apply t₂.hom.op ((CatFiberedInGroupoids.homFunctor g.hom).map k).op m

end Arrow

end Transport

section SchemeStackHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U : BigFppfOver B S hS}

/-- Restriction of functions along an arrow of the stack of a scheme is the map on global
sections of the underlying morphism of schemes. -/
theorem schemeStack_structureSheaf_map_apply
    {u₁ u₂ : (schemeStack.{u, w} B S hS U).val.val.obj} (k : u₁ ⟶ u₂)
    (c : FibredSite.objRing B S hS (schemeStack.{u, w} B S hS U).val.val.p u₂) :
    (((FibredSite.ringStructureSheafCore B S hS (schemeStack.{u, w} B S hS U).val.val.p
      (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids .fppf).obj.map k.op).hom c :
        FibredSite.objRing B S hS (schemeStack.{u, w} B S hS U).val.val.p u₁) =
      ((BigFppfOver.toScheme B S hS).map
        ((schemeStack.{u, w} B S hS U).val.val.p.map k)).appTop c :=
  rfl

/-- **A ring map between the functions of two objects of the stack of an affine scheme `U`,
compatible with the global functions of `U`, comes from an arrow.** For objects `u₁`, `u₂` of
`Sch/U` with `u₂` affine and a ring map `θ : Γ(u₂) ⟶ Γ(u₁)` over `Γ(U)`, there is an arrow
`k : u₁ ⟶ u₂` of `Sch/U` whose map on functions is `θ`. -/
theorem exists_schemeStack_hom_of_ringHom (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {u₁ u₂ : Over U}
    (h₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((schemeStack.{u, w} B S hS U).val.val.p.obj u₂)))
    (θ : FibredSite.objRing B S hS (schemeStack.{u, w} B S hS U).val.val.p u₂ →+*
      FibredSite.objRing B S hS (schemeStack.{u, w} B S hS U).val.val.p u₁)
    (hθ : ∀ a, θ (restrictGlobal (𝒰 := schemeStack.{u, w} B S hS U) Over.mkIdTerminal u₂ a) =
      restrictGlobal (𝒰 := schemeStack.{u, w} B S hS U) Over.mkIdTerminal u₁ a) :
    ∃ k : u₁ ⟶ u₂, ∀ c, ((FibredSite.ringStructureSheafCore B S hS
      (schemeStack.{u, w} B S hS U).val.val.p (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
        .fppf).obj.map k.op).hom c = θ c := by
  let W₁ := (BigFppfOver.toScheme B S hS).obj u₁.left
  let W₂ := (BigFppfOver.toScheme B S hS).obj u₂.left
  have : IsAffine W₂ := h₂
  let φ : W₁ ⟶ W₂ := W₁.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ W₂.isoSpec.inv
  have hφ : φ.appTop = CommRingCat.ofHom θ :=
    Scheme.appTop_toSpecΓ_comp_Spec_map_comp_isoSpec_inv (CommRingCat.ofHom θ)
  have hU' : φ ≫ (BigFppfOver.toScheme B S hS).map u₂.hom =
      (BigFppfOver.toScheme B S hS).map u₁.hom := by
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.comp_appTop, hφ]
    ext a
    have e₁ : (Over.mkIdTerminal.from u₁).left = u₁.hom := by simp
    have e₂ : (Over.mkIdTerminal.from u₂).left = u₂.hom := by simp
    have h := hθ a
    change θ (((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from u₂).left).appTop a) =
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from u₁).left).appTop a at h
    rwa [e₁, e₂] at h
  have hl : ∀ v : Over U, B.inclusion.map v.left.hom =
      (BigFppfOver.toScheme B S hS).map v.hom ≫ B.inclusion.map U.hom :=
    fun v => (congrArg B.inclusion.map (Over.w v.hom)).symm.trans (B.inclusion.map_comp _ _)
  let kl : u₁.left ⟶ u₂.left := Over.homMk (B.inclusion.preimage φ) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage, hl, hl, ← Category.assoc, hU'])
  let k : u₁ ⟶ u₂ := Over.homMk kl (by
    refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    change B.inclusion.map (B.inclusion.preimage φ ≫ u₂.hom.left) = B.inclusion.map u₁.hom.left
    rw [Functor.map_comp, Functor.map_preimage]
    exact hU')
  refine ⟨k, fun c => ?_⟩
  change (B.inclusion.map (B.inclusion.preimage φ)).appTop c = θ c
  rw [Functor.map_preimage, hφ]
  rfl

end SchemeStackHom

/-- A morphism `inv c ≫ ζ` is compatible with maps out of its target as soon as `c` and `ζ` are. -/
theorem _root_.CategoryTheory.Functor.map_inv_comp_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {a b d : 𝒞} (c : a ⟶ b) [IsIso c] (ζ : a ⟶ d) {E : 𝒟}
    (e₁ : F.obj b ⟶ E) (e₂ : F.obj d ⟶ E) (h : F.map ζ ≫ e₂ = F.map c ≫ e₁) :
    F.map (inv c ≫ ζ) ≫ e₂ = e₁ := by
  rw [F.map_comp, Category.assoc, h, ← Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id,
    Category.id_comp]

/-- A morphism which, after a conservative functor, is an isomorphism up to isomorphisms is an
isomorphism. -/
theorem _root_.CategoryTheory.Functor.isIso_of_map_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (F : 𝒞 ⥤ 𝒟) [F.ReflectsIsomorphisms] {a b d : 𝒞} (c : a ⟶ b) [IsIso c]
    (z : a ⟶ d) {E : 𝒟} (e₁ : F.obj b ≅ E) (e₂ : F.obj d ≅ E)
    (h : F.map z ≫ e₂.hom = F.map c ≫ e₁.hom) : IsIso z := by
  have : IsIso (F.map z) := by
    rw [(Iso.eq_comp_inv e₂).2 h]
    infer_instance
  exact isIso_of_reflects_iso z F

/-- Restriction along `inv c ≫ ζ` inverts restriction along `c`, given the restrictions along `ζ`
and `c` agree. -/
theorem _root_.PresheafOfModules.map_inv_comp_apply_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} (P : PresheafOfModules R) {a b d : C} (c : a ⟶ b) [IsIso c] (ζ : a ⟶ d)
    (m : P.obj (op d)) (w : P.obj (op b)) (h : P.map ζ.op m = P.map c.op w) :
    P.map (inv c ≫ ζ).op m = w := by
  have hc : c.op ≫ (inv c).op = 𝟙 (op b) := by rw [← op_comp, IsIso.inv_hom_id, op_id]
  rw [op_comp, P.map_comp_apply, h]
  exact (P.map_comp_apply c.op (inv c).op w).symm.trans ((P.congr_map_apply hc w).trans
    (by simp only [PresheafOfModules.map_id]; rfl))

section PointMorphisms

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R : Type u} [CommRing R] {x₁ x₂ y : 𝒳.val.val.obj}
  (e₁ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₁) ≅ Spec (CommRingCat.of R))
  (e₂ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₂) ≅ Spec (CommRingCat.of R))

/-- **Two arrows into points over `Spec R` lie over the same morphism to `Spec R` as soon as
they pull back the functions of `R` in the same way.** -/
theorem toScheme_map_comp_eq_of_pointRingHom (ψ₁ : y ⟶ x₁) (ψ₂ : y ⟶ x₂)
    (h : ∀ r : R, (fppfStructurePresheaf B S hS 𝒳).map ψ₂.op (pointRingHom B S hS 𝒳 x₂ e₂ r) =
      (fppfStructurePresheaf B S hS 𝒳).map ψ₁.op (pointRingHom B S hS 𝒳 x₁ e₁ r)) :
    (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ₂) ≫ e₂.hom =
      (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ₁) ≫ e₁.hom := by
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun r' => ?_))
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv r = r' :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom r', by simp⟩
  exact h r

/-- **A 2-arrow from an isomorphic pair of arrows out of a common object.** If `c : y ⟶ x₁` and
`ζ : y ⟶ x₂` are isomorphisms lying over the same morphism to `Spec R`, and restriction along `ζ`
is restriction along `c` after `t⁻¹ : x₂^* ⟶ x₁^*`, then `c⁻¹ ≫ ζ` is a 2-arrow inducing `t`. -/
theorem exists_pointPullbackTransportIso_eq_of_restriction (c : y ⟶ x₁) [IsIso c] (ζ : y ⟶ x₂)
    [IsIso ζ] (hbase : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ζ) ≫ e₂.hom =
      (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map c) ≫ e₁.hom)
    (t : pointPullback B S hS 𝒳 x₁ e₁ ≅ pointPullback B S hS 𝒳 x₂ e₂)
    (hζ : ∀ (M : quasicoherentModules B S hS 𝒳) (m : (pointPullback B S hS 𝒳 x₂ e₂).obj M),
      (M.obj.val.map ζ.op).hom m = (M.obj.val.map c.op).hom ((t.inv.app M).hom m)) :
    ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ e₂.hom =
        e₁.hom), pointPullbackTransportIso B S hS 𝒳 e₁ e₂ a ha = t :=
  ⟨(asIso c).symm ≪≫ asIso ζ, (𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).map_inv_comp_comp_eq
    c ζ e₁.hom e₂.hom hbase, Iso.ext ((Iso.inv_eq_inv _ _).1 (NatTrans.ext (funext fun M =>
      ModuleCat.hom_ext (LinearMap.ext fun m => M.obj.val.map_inv_comp_apply_eq c ζ m _
        (hζ M m)))))⟩

variable (B S hS) in
/-- **Stacks 0GRP, for points over `Spec R` given by isomorphisms with `Spec R`.** Let `𝒳` be an
algebraic stack with affine (absolute) diagonal and `x₁`, `x₂` two points of `𝒳` lying over
schemes identified with `Spec R` by `e₁`, `e₂`. Every isomorphism of tensor functors
`t : x₁^* ≅ x₂^*` between the pullbacks `QCoh(𝒪_𝒳) ⥤ Mod_R` is induced by a 2-arrow
`a : x₁ ≅ x₂` compatible with `e₁`, `e₂`. -/
theorem exists_iso_pointPullbackTransportIso_eq
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (t : pointPullback B S hS 𝒳 x₁ e₁ ≅ pointPullback B S hS 𝒳 x₂ e₂)
    [NatTrans.IsMonoidal t.hom] :
    ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ e₂.hom =
        e₁.hom), pointPullbackTransportIso B S hS 𝒳 e₁ e₂ a ha = t := by
  classical
  have hUa : IsAffineOver B S hS (𝒳.val.val.p.obj x₁) := isAffine_point B S hS 𝒳 x₁ e₁
  obtain ⟨g, hg, c, hcU⟩ : ∃ (g : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₁) ⟶ 𝒳)
      (_ : IsAffineHom B S hS g)
      (c : (CatFiberedInGroupoids.homFunctor g.hom).obj (Over.mk (𝟙 (𝒳.val.val.p.obj x₁))) ⟶ x₁),
      𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x₁)) c :=
    ⟨fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj x₁) ⟨x₁, rfl⟩,
      isAffineHom_of_isAffineHom_diagonal_viewOverIntegers B S hS (contains_terminalScheme B) hUa
        hΔ _,
      (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (𝒳.val.val.p.obj x₁)
        ⟨x₁, rfl⟩ (Over.mk (𝟙 (𝒳.val.val.p.obj x₁)))).φ,
      (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (𝒳.val.val.p.obj x₁)
        ⟨x₁, rfl⟩ (Over.mk (𝟙 (𝒳.val.val.p.obj x₁)))).isStronglyCartesian.toIsHomLift⟩
  obtain ⟨t₁, ⟨ht₁⟩, hx₁⟩ := exists_isTerminal_costructuredArrow_of_isAffineHom B S hS g hg x₁
    (isAffine_point B S hS 𝒳 x₁ e₁)
  obtain ⟨t₂, ⟨ht₂⟩, hx₂⟩ := exists_isTerminal_costructuredArrow_of_isAffineHom B S hS g hg x₂
    (isAffine_point B S hS 𝒳 x₂ e₂)
  have hθA : ∀ a, pointTransportRingHom hg e₁ e₂ ht₁ ht₂ t
      (restrictGlobal (𝒰 := schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₁)) Over.mkIdTerminal
          t₂.left a) =
      restrictGlobal (𝒰 := schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₁)) Over.mkIdTerminal
          t₁.left a := fun a => by
    have h := pointTransportFun_mul_restrictGlobal hg e₁ e₂ t.inv ht₁ ht₂
      (Over.mkIdTerminal (X := 𝒳.val.val.p.obj x₁)) a 1
    rwa [one_mul, pointTransportFun_one, one_mul] at h
  obtain ⟨k, hk⟩ := exists_schemeStack_hom_of_ringHom.{u, w} hUa hx₂ _ hθA
  have hC := map_homFunctor_comp_terminal_apply hg e₁ e₂ t.inv ht₁ ht₂
    (Over.mkIdTerminal (X := 𝒳.val.val.p.obj x₁)) hUa hx₂ hk
  have : IsIso c :=
    𝒳.val.isFiberedInGroupoids.isIso_of_isHomLift_isIso (𝟙 (𝒳.val.val.p.obj x₁)) c
  have hs := CostructuredArrow.w (ht₁.from (CostructuredArrow.mk c))
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, ζ = (CatFiberedInGroupoids.homFunctor g.hom).map
      (ht₁.from (CostructuredArrow.mk c)).left ≫ (CatFiberedInGroupoids.homFunctor g.hom).map k ≫
        t₂.hom := ⟨_, rfl⟩
  have hζ : ∀ (M : quasicoherentModules B S hS 𝒳) (m : (pointPullback B S hS 𝒳 x₂ e₂).obj M),
      (M.obj.val.map ζ.op).hom m = (M.obj.val.map c.op).hom ((t.inv.app M).hom m) := fun M m => by
    subst hζdef
    erw [op_comp, M.obj.val.map_comp_apply, hC M m, ← M.obj.val.map_comp_apply, ← op_comp]
    exact congrArg (fun φ : (CatFiberedInGroupoids.homFunctor g.hom).obj
      (Over.mk (𝟙 (𝒳.val.val.p.obj x₁))) ⟶ x₁ => (M.obj.val.map φ.op).hom ((t.inv.app M).hom m)) hs
  have hbase : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ζ) ≫ e₂.hom =
      (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map c) ≫ e₁.hom := by
    refine toScheme_map_comp_eq_of_pointRingHom e₁ e₂ c ζ fun r => ?_
    have h1 := hζ (𝟙_ _) ((Functor.LaxMonoidal.ε (pointPullback B S hS 𝒳 x₂ e₂)).hom r)
    have h2 : (t.inv.app (𝟙_ _)).hom ((Functor.LaxMonoidal.ε (pointPullback B S hS 𝒳 x₂ e₂)).hom
        r) =
        (Functor.LaxMonoidal.ε (pointPullback B S hS 𝒳 x₁ e₁)).hom r :=
      congrArg (fun φ => φ.hom r) (NatTrans.IsMonoidal.unit (τ := t.inv))
    exact (congrArg ((𝟙_ (quasicoherentModules B S hS 𝒳)).obj.val.map ζ.op).hom
      (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x₂ e₂) r)).symm.trans
      (h1.trans (congrArg ((𝟙_ (quasicoherentModules B S hS 𝒳)).obj.val.map c.op).hom
        (h2.trans (ModuleCat.restrictScalars_η (pointRingHom B S hS 𝒳 x₁ e₁) r))))
  have : IsIso (𝒳.val.val.p.map c) := Functor.map_isIso _ c
  have : IsIso (𝒳.val.val.p.map ζ) := (BigFppfOver.toScheme B S hS).isIso_of_map_comp_eq
    (𝒳.val.val.p.map c) (𝒳.val.val.p.map ζ) e₁ e₂ hbase
  have : IsIso ζ := 𝒳.val.isFiberedInGroupoids.isIso_of_isHomLift_isIso (𝒳.val.val.p.map ζ) ζ
  exact exists_pointPullbackTransportIso_eq_of_restriction e₁ e₂ c ζ hbase t hζ

end PointMorphisms

section OverSpec

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (CommRingCat.of R))}

/-- **Stacks 0GRP.** Let `𝒳` be an algebraic stack with affine diagonal and `B` a ring. Let
`f₁, f₂ : Spec B ⟶ 𝒳` be two morphisms, given as points `x₁`, `x₂` of `𝒳` over `Spec B`, with
structure morphisms `q₁, q₂ : Spec B ⟶ S`, and let `t : f₁^* ≅ f₂^*` be an isomorphism of the
tensor functors `f_i^* : QCoh(𝒪_𝒳) ⥤ Mod_B`
    (`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback`,
a braided monoidal additive functor; `t` is monoidal). Then `q₁ = q₂`, and there is a 2-arrow
`f₁ ⟶ f₂`, an isomorphism `a : x₁ ≅ x₂` lying over the identity of `Spec B`, inducing `t`.

"Affine diagonal" is absolute, as in the source (Morphisms of Stacks, Definition 050D): it is the
diagonal of the view of `𝒳` over `Spec ℤ`,
    `AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`.
The structure morphisms to `S` are not assumed equal: that they agree is part of the conclusion,
read off from the functions `B ⟶ Γ(x_i, 𝒪)` which `t` preserves (it is monoidal). The form with
equal structure morphisms is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullbackTransportIso_eq_of_over`.

The proof does not follow the source's chart and descent, but takes the chart `g = f₁ : Spec B ⟶ 𝒳`
itself (affine, the diagonal being affine): with `W_i = Spec B ×_{f_i, 𝒳, f₁} Spec B` and
`g_*𝒪 = g_{QCoh,*}𝒪_{Spec B}`, `f_i^*(g_*𝒪) = Γ(W_i)`, and `t` gives a ring isomorphism
`Γ(W₂) ⟶ Γ(W₁)` over both copies of `B` (it is monoidal and natural, the multiplication of
`g_*𝒪` being `AlgebraicGeometry.Stack.AlgebraicStacks.affineDirectImageMul`), hence an arrow
`W₁ ⟶ W₂`; the image of the identity 2-arrow of `f₁` in `W₁` is the 2-arrow `f₁ ≅ f₂`. That it
induces `t` follows from naturality of `t` and the units `M ⟶ g_* g^* M`. This is the content of
Stacks 0GRK (the algebra `C = F(g_{QCoh,*}𝒪_U)` with its map `A ⟶ C`) for the point pullbacks,
computed directly. -/
@[stacks 0GRP "points over possibly different structure morphisms; they agree"]
theorem eq_and_exists_iso_pointPullbackTransportIso_eq
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
    (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
    (t : pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁) ≅
      pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂)) [NatTrans.IsMonoidal t.hom] :
    q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
      pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁) (overSpecIso B S hS 𝒳 hx₂)
        a ha = t := by
  obtain ⟨a, ha, hat⟩ := exists_iso_pointPullbackTransportIso_eq B S hS _ _ hΔ t
  refine ⟨?_, a, ha, hat⟩
  let φ : Over.mk q₁ ⟶ Over.mk q₂ := eqToHom hx₁.symm ≫ 𝒳.val.val.p.map a.hom ≫ eqToHom hx₂
  have hφ : (BigFppfOver.toScheme B S hS).map φ = 𝟙 _ := by
    have ha' : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        eqToHom (congrArg (BigFppfOver.toScheme B S hS).obj hx₂) =
          eqToHom (congrArg (BigFppfOver.toScheme B S hS).obj hx₁) := ha
    simp only [φ, Functor.map_comp, eqToHom_map]
    rw [ha', eqToHom_trans, eqToHom_refl]
  have hl : φ.left = 𝟙 _ := B.inclusion.map_injective (hφ.trans (B.inclusion.map_id _).symm)
  simpa [hl] using (Over.w φ).symm

/-- **Stacks 0GRP, with equal structure morphisms** (the source's statement). Let `𝒳` be an
algebraic stack with affine diagonal (over `Spec ℤ`), `B` a ring and `f₁, f₂ : Spec B ⟶ 𝒳` two
morphisms over `S`, given as points `x₁`, `x₂` of `𝒳` lying over the same object `Spec B ⟶ S` of
the site. Every isomorphism `t : f₁^* ≅ f₂^*` of the tensor functors
`f_i^* : QCoh(𝒪_𝒳) ⥤ Mod_B` is induced by a 2-arrow `f₁ ⟶ f₂`: an isomorphism `a : x₁ ≅ x₂` of
the fibre over `Spec B`. -/
@[stacks 0GRP "the source's form, with equal structure morphisms"]
theorem exists_iso_pointPullbackTransportIso_eq_of_over
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {q : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
    (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q)
    (t : pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁) ≅
      pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂)) [NatTrans.IsMonoidal t.hom] :
    ∃ (a : x₁ ≅ x₂) (ha : 𝒳.val.val.p.map a.hom = eqToHom (hx₁.trans hx₂.symm)),
      pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁) (overSpecIso B S hS 𝒳 hx₂)
        a (toScheme_map_comp_overSpecIso B S hS 𝒳 hx₁ hx₂ a ha) = t := by
  obtain ⟨-, a, ha, hat⟩ := eq_and_exists_iso_pointPullbackTransportIso_eq B S hS hΔ hx₁ hx₂ t
  have hp : 𝒳.val.val.p.map a.hom = eqToHom (hx₁.trans hx₂.symm) := by
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [eqToHom_map]
    refine (Iso.eq_comp_inv _).2 ha |>.trans ?_
    simp [overSpecIso]
  exact ⟨a, hp, hat⟩

end OverSpec

end AlgebraicGeometry.Stack.AlgebraicStacks
