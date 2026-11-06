module

public import StacksFrontier.Algebra.Category.ModuleCat.EssSurjOfFreeObject
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSectionsColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineModuleExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines

/-!
# Quasi-coherent modules on a category fibred in groupoids with a final affine object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids with a final object `x₀` lying
over an affine scheme `Spec A` — for instance the big fppf site `(Sch/U)_{fppf}` of an affine
scheme `U = Spec A` over `S`, viewed as a category fibred in groupoids over `(Sch/S)_{fppf}`.
Then taking sections over `x₀` is an equivalence `QCoh(𝒪_𝒳) ≌ Mod_A`.

* **Faithful.** Over an affine object `y` the sections `ℱ(y)` are generated over `Γ(y)` by the
  restrictions of the sections over `x₀` (Descent, Proposition 03DX, in the form
  `AlgebraicGeometry.FibredSite.semilinearMap_ext_of_restriction`), so two maps agreeing over
  `x₀` agree over every affine object, and restriction to the affine objects is faithful.
* **Full.** A linear map `θ : ℱ(x₀) ⟶ 𝒢(x₀)` extends uniquely along the arrow `y ⟶ x₀` to a
  `Γ(y)`-linear map `ℱ(y) ⟶ 𝒢(y)` for each affine `y`
  (`AlgebraicGeometry.FibredSite.extendAlong`), compatibly with restriction, so to a morphism of
  the restrictions to the affine subcategory `𝒳_{affine}`, and restriction to `𝒳_{affine}` is an
  equivalence (Stacks 0H0B, 0H0C).
* **Essentially surjective.** Sections over `x₀` commute with colimits of quasi-coherent modules
  (`AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentEvaluation`) and send
  `𝒪_𝒳` to `A`; an `A`-module is the cokernel of a map of free modules, which lifts by fullness.

## Main results

* `AlgebraicGeometry.FibredSite.faithful_quasicoherentEvaluation_of_isTerminal` and
  `AlgebraicGeometry.FibredSite.full_quasicoherentEvaluation_of_isTerminal`: sections over a
  final object lying over an affine scheme form a fully faithful functor on `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.FibredSite.isEquivalence_quasicoherentEvaluation_of_isTerminal`: **it is an
  equivalence `QCoh(𝒪_𝒳) ≌ Mod_{𝒪(x₀)}`.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.FibredSite

open Stack Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [EssentiallySmall.{u} 𝒳] {x₀ : 𝒳} (h₀ : IsTerminal x₀)
  (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₀)))

omit [EssentiallySmall.{u} 𝒳] in
include h₀ ha in
/-- **Sections over a final object lying over an affine scheme are faithful on quasi-coherent
modules.** -/
theorem faithful_quasicoherentEvaluation_of_isTerminal :
    ((SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op x₀)).Faithful where
  map_injective {M N} f g hfg := by
    have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
    let Res := Stacks.DenseSubsiteModules.moduleRestriction
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (Stack.AffineCategory.inclusion B S hS p) (ringStructureSheafCore B S hS p hp .fppf)
    apply ObjectProperty.hom_ext
    apply Res.map_injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro y
    apply ModuleCat.hom_ext
    let n : y.unop.obj ⟶ x₀ := h₀.from _
    let := objModule B S hS p hp M.obj y.unop.obj
    let := objModule B S hS p hp N.obj y.unop.obj
    exact semilinearMap_ext_of_restriction (M := M.obj) M.property n ha y.unop.property
      (σ := RingHom.id _) (θ₁ := (f.hom.val.app (op y.unop.obj)).hom)
      (θ₂ := (g.hom.val.app (op y.unop.obj)).hom) fun s => by
        show f.hom.val.app (op y.unop.obj) (M.obj.val.map n.op s) =
          g.hom.val.app (op y.unop.obj) (M.obj.val.map n.op s)
        rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
        exact congrArg (N.obj.val.map n.op) (ConcreteCategory.congr_hom hfg s)

omit [EssentiallySmall.{u} 𝒳] in
include h₀ ha in
/-- Extending a linear map `θ : ℱ(x₀) ⟶ 𝒢(x₀)` along the arrow `x₀ ⟶ x₀` gives back `θ`. -/
theorem extendAlong_from_self_of_isTerminal
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite)
    (N : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    letI := objModule B S hS p hp M x₀
    letI := objModule B S hS p hp N x₀
    ∀ (θ : M.val.obj (op x₀) →ₗ[objRing B S hS p x₀] N.val.obj (op x₀)) (t : M.val.obj (op x₀)),
      letI := objAlgebra B S hS p (h₀.from x₀)
      letI : Module (objRing B S hS p x₀) (N.val.obj (op x₀)) :=
        Module.compHom _ (algebraMap (objRing B S hS p x₀) (objRing B S hS p x₀))
      extendAlong M hM (h₀.from x₀) ha ha N ((restrictionLinear N (h₀.from x₀)).comp θ) t =
        θ t := by
  intro θ t
  have hid : h₀.from x₀ = 𝟙 x₀ := h₀.hom_ext _ _
  have ht : M.val.map (h₀.from x₀).op t = t :=
    (M.val.congr_map_apply (congrArg Quiver.Hom.op hid) t).trans (by simp; rfl)
  have := let := objModule B S hS p hp M x₀
    let := objModule B S hS p hp N x₀
    let := objAlgebra B S hS p (h₀.from x₀)
    let : Module (objRing B S hS p x₀) (N.val.obj (op x₀)) :=
      Module.compHom _ (algebraMap (objRing B S hS p x₀) (objRing B S hS p x₀))
    extendAlong_map M hM (h₀.from x₀) ha ha N ((restrictionLinear N (h₀.from x₀)).comp θ) t
  rw [ht] at this
  refine this.trans ?_
  show N.val.map (h₀.from x₀).op (θ t) = θ t
  exact (N.val.congr_map_apply (congrArg Quiver.Hom.op hid) _).trans (by simp; rfl)

omit [EssentiallySmall.{u} 𝒳] in
include h₀ ha in
/-- **Sections over a final object lying over an affine scheme are full on quasi-coherent
modules.** A linear map `θ : ℱ(x₀) ⟶ 𝒢(x₀)` extends along the arrow `y ⟶ x₀` from every affine
object `y`, compatibly with restriction, to a morphism of the restrictions to the affine
subcategory, which comes from a morphism `ℱ ⟶ 𝒢` because restriction to the affine subcategory
is an equivalence. -/
theorem full_quasicoherentEvaluation_of_isTerminal :
    ((SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op x₀)).Full where
  map_surjective {M N} θ := by
    have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
    have := isEquivalence_moduleRestriction B S hS p hp (siteKindRingedSite B S hS p hp .fppf).J
      (BigFppfOver.associatedTopology B S hS p .fppf) (ringStructureSheafCore B S hS p hp .fppf)
    let Res := Stacks.DenseSubsiteModules.moduleRestriction
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (Stack.AffineCategory.inclusion B S hS p) (ringStructureSheafCore B S hS p hp .fppf)
    let := objModule B S hS p hp M.obj x₀
    let := objModule B S hS p hp N.obj x₀
    let θ₀ : M.obj.val.obj (op x₀) →ₗ[objRing B S hS p x₀] N.obj.val.obj (op x₀) := θ.hom
    -- the extension of `θ` to an affine object
    let extHom (y : 𝒳) (hy : IsAffineOver B S hS (p.obj y)) :
        M.obj.val.obj (op y) ⟶ N.obj.val.obj (op y) :=
      let := objModule B S hS p hp M.obj y
      let := objModule B S hS p hp N.obj y
      let := objAlgebra B S hS p (h₀.from y)
      let : Module (objRing B S hS p x₀) (N.obj.val.obj (op y)) :=
        Module.compHom _ (algebraMap (objRing B S hS p x₀) (objRing B S hS p y))
      ModuleCat.ofHom (extendAlong M.obj M.property (h₀.from y) ha hy N.obj
        ((restrictionLinear N.obj (h₀.from y)).comp θ₀))
    have hext (y z : 𝒳) (k : z ⟶ y) (hy : IsAffineOver B S hS (p.obj y))
        (hz : IsAffineOver B S hS (p.obj z)) (t : M.obj.val.obj (op y)) :
        N.obj.val.map k.op (extHom y hy t) = extHom z hz (M.obj.val.map k.op t) :=
      let := objModule B S hS p hp M.obj y
      let := objModule B S hS p hp N.obj y
      let := objModule B S hS p hp N.obj z
      let := objAlgebra B S hS p (h₀.from y)
      let := objAlgebra B S hS p (h₀.from z)
      let : Module (objRing B S hS p x₀) (N.obj.val.obj (op y)) :=
        Module.compHom _ (algebraMap (objRing B S hS p x₀) (objRing B S hS p y))
      let : Module (objRing B S hS p x₀) (N.obj.val.obj (op z)) :=
        Module.compHom _ (algebraMap (objRing B S hS p x₀) (objRing B S hS p z))
      map_extendAlong' M.obj M.property (h₀.from y) ha hy N.obj k (h₀.from z)
        (h₀.hom_ext _ _) hz _ _ (fun s => by
          show N.obj.val.map (h₀.from z).op (θ₀ s) =
            N.obj.val.map k.op (N.obj.val.map (h₀.from y).op (θ₀ s))
          rw [h₀.hom_ext (h₀.from z) (k ≫ h₀.from y), op_comp]
          exact N.obj.val.map_comp_apply _ _ _) t
    let fA : Res.obj M.obj ⟶ Res.obj N.obj :=
      ⟨{ app := fun y => extHom y.unop.obj y.unop.property
         naturality := fun {y z} k => by
           ext t
           exact (hext y.unop.obj z.unop.obj k.unop.hom y.unop.property z.unop.property t).symm }⟩
    refine ⟨ObjectProperty.homMk (Res.preimage fA), ModuleCat.hom_ext (LinearMap.ext fun t => ?_)⟩
    exact (ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.val.app (op ⟨x₀, ha⟩)) (Res.map_preimage fA)) t).trans
      (extendAlong_from_self_of_isTerminal B S hS p hp h₀ ha M.obj M.property N.obj θ₀ t)

include h₀ ha in
/-- **Quasi-coherent modules on a category fibred in groupoids with a final object `x₀` lying
over an affine scheme are the modules over the ring of functions of `x₀`.** Taking sections over
`x₀` is an equivalence `QCoh(𝒪_𝒳) ≌ Mod_{𝒪(x₀)}`: it is fully faithful, commutes with colimits,
and sends `𝒪_𝒳` to `𝒪(x₀)`. -/
theorem isEquivalence_quasicoherentEvaluation_of_isTerminal :
    ((SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op x₀)).IsEquivalence := by
  have := faithful_quasicoherentEvaluation_of_isTerminal B S hS p hp h₀ ha
  have := full_quasicoherentEvaluation_of_isTerminal B S hS p hp h₀ ha
  have := preservesColimitsOfSize_quasicoherentEvaluation B S hS p hp ha
  have : PreservesColimitsOfSize.{0, 0} ((SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op x₀)) := preservesColimitsOfSize_shrink _
  have hC := hasColimitsOfSize_quasicoherentModules' B S hS p hp
  have : HasCoproducts.{u} (SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).FullSubcategory :=
    fun _ => hC.has_colimits_of_shape _
  have := ModuleCat.essSurj_of_full_of_preservesColimits
    ((SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).ι ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op x₀))
    ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩ (Iso.refl _)
  exact { }

end AlgebraicGeometry.FibredSite

end
