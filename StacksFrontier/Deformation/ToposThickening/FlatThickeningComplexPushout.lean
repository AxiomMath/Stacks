module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexPulledLift

/-!
# The pushout `ℱ'₂ ⊔_{I₂ ⊗ ℱ} (I₁ ⊗ ℱ)` of Stacks 08VY, as an `O'₁`-module

In Situation **Stacks 08VX**, presented on one site as
`Deformation.ToposThickening.FlatThickeningComplexSituation`, the flat lift `ℱ'₂` of `ℱ` across
the middle column is an extension `0 ⟶ I₂ ⊗ ℱ ⟶ ℱ'₂ ⟶ ℱ ⟶ 0` of `O'₂`-modules. Its pushout along
the map `I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` induced by the first morphism `h` of the upper row is an extension of
`ℱ` by `I₁ ⊗ ℱ`. It is annihilated by the kernel of `h^♯ : O'₂ ⟶ O'₁`, which is the ideal of
`h` as a first order thickening of `(Sh(C'₁), O'₁)`, so it descends to an `O'₁`-module; that
module is `h^*ℱ'₂`.

## Main definitions

* `Deformation.ToposThickening.FlatThickeningComplexSituation.pushoutDescent`: the descent of the
  pushout to an extension `0 ⟶ I₁ ⊗ ℱ ⟶ P ⟶ ℱ ⟶ 0` of `O'₁`-modules.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.pulledToPushoutDescent`: the map
  `h^*ℱ'₂ ⟶ P` adjoint to the inclusion of `ℱ'₂` into the pushout.

## Main results

* `Deformation.ToposThickening.FlatThickeningComplexSituation.isLocallySurjective_hSharp`: the map
  `h^♯ : O'₂ ⟶ O'₁` of a short exact sequence of first order thickenings is locally surjective.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.isIso_pulledToPushoutDescent`:
  `h^*ℱ'₂` is the descended pushout.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.pushoutDescent_actionMap`: the
  canonical action of `I₁` on the descended pushout is the identity.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₂ u₂ w vB uB wB vB' uB' wB'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

section Comparison

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- A morphism whose composite with the unit of an adjunction vanishes is killed by the left
adjoint. -/
theorem _root_.CategoryTheory.Adjunction.map_eq_zero_of_comp_unit_eq_zero {ℬ : Type*} [Category ℬ]
    [Preadditive ℬ] {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj : L ⊣ R) [L.PreservesZeroMorphisms]
    [R.PreservesZeroMorphisms] {M N : 𝒜} (f : M ⟶ N) (hf : f ≫ adj.unit.app N = 0) :
    L.map f = 0 := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero, ← hf]
  exact (adj.unit.naturality f).symm

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- **A comparison from a right exact sequence to a short exact sequence is an isomorphism**, if
it is an isomorphism on the cokernel terms and an epimorphism on the kernel terms whose kernel the
first map of the right exact sequence kills. -/
theorem isIso_of_rightExact_comparison {A B C : 𝒜} (a : A ⟶ B) (q : B ⟶ C)
    (haq : a ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q haq)) (S' : ShortComplex 𝒜)
    (hS' : S'.ShortExact) (α : A ⟶ S'.X₁) [Epi α] (β : B ⟶ S'.X₂) (γ : C ⟶ S'.X₃) [IsIso γ]
    (h₁ : a ≫ β = α ≫ S'.f) (h₂ : β ≫ S'.g = q ≫ γ)
    (hker : ∀ {Z : 𝒜} (z : Z ⟶ A), z ≫ α = 0 → z ≫ a = 0) : IsIso β := by
  have hα := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel α)
  obtain ⟨a₀, ha₀⟩ := CokernelCofork.IsColimit.desc' hα a (hker _ (kernel.condition α))
  change α ≫ a₀ = a at ha₀
  have hm : a₀ ≫ β = S'.f := by
    rw [← cancel_epi α, ← Category.assoc, ha₀, h₁]
  have := hS'.mono_f
  have : Mono a₀ := mono_of_mono_fac hm
  have hz : a₀ ≫ q = 0 := by rw [← cancel_epi α, ← Category.assoc, ha₀, haq, comp_zero]
  have : Epi q := ⟨fun g₁ g₂ h ↦ Cofork.IsColimit.hom_ext hq h⟩
  have hcok : IsColimit (CokernelCofork.ofπ q hz) :=
    CokernelCofork.IsColimit.ofπ' _ _ fun {T} g hg ↦
      ⟨(CokernelCofork.IsColimit.desc' hq g (by rw [← ha₀, Category.assoc, hg, comp_zero])).1,
        (CokernelCofork.IsColimit.desc' hq g (by rw [← ha₀, Category.assoc, hg, comp_zero])).2⟩
  have hT : (ShortComplex.mk a₀ q hz).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ hcok
      mono_f := inferInstance
      epi_g := inferInstance }
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    (S₁ := ShortComplex.mk a₀ q hz) (S₂ := S')
    { τ₁ := 𝟙 _
      τ₂ := β
      τ₃ := γ
      comm₁₂ := by simpa using hm.symm
      comm₂₃ := h₂ } hT hS' inferInstance inferInstance

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- **The transpose of a comparison of extensions along an adjunction is an isomorphism.** Let
`L ⊣ R` with `L` a left adjoint between abelian categories, `0 ⟶ K ⟶ M ⟶ Q ⟶ 0` short exact in
the source, `0 ⟶ K' ⟶ N ⟶ Q' ⟶ 0` short exact in the target, and `u : M ⟶ R N` a map restricting
to `κ : K ⟶ R K'` and inducing `φ : Q ⟶ R Q'`. If the transpose of `φ` is an isomorphism, the
transpose of `κ` an epimorphism whose kernel is killed by `L K ⟶ L M`, then the transpose of `u`
is an isomorphism. -/
theorem isIso_homEquiv_symm_of_extensions {ℬ : Type*} [Category ℬ] [Abelian ℬ] {L : 𝒜 ⥤ ℬ}
    {R : ℬ ⥤ 𝒜} (adj : L ⊣ R) [L.IsLeftAdjoint] (S : ShortComplex 𝒜) (hS : S.ShortExact)
    (S' : ShortComplex ℬ) (hS' : S'.ShortExact) (u : S.X₂ ⟶ R.obj S'.X₂)
    (κ : S.X₁ ⟶ R.obj S'.X₁) (φ : S.X₃ ⟶ R.obj S'.X₃)
    (hu : S.f ≫ u = κ ≫ R.map S'.f) (hug : u ≫ R.map S'.g = S.g ≫ φ)
    [Epi ((adj.homEquiv _ _).symm κ)] [IsIso ((adj.homEquiv _ _).symm φ)]
    (hker : ∀ {Z : ℬ} (z : Z ⟶ L.obj S.X₁), z ≫ (adj.homEquiv _ _).symm κ = 0 →
      z ≫ L.map S.f = 0) :
    IsIso ((adj.homEquiv _ _).symm u) := by
  have haq : L.map S.f ≫ L.map S.g = 0 := by rw [← L.map_comp, S.zero, L.map_zero]
  have hq : IsColimit (CokernelCofork.ofπ (L.map S.g) haq) :=
    isColimitCoforkMapOfIsColimit' L S.zero hS.gIsCokernel
  refine isIso_of_rightExact_comparison (L.map S.f) (L.map S.g) haq hq S' hS'
    ((adj.homEquiv _ _).symm κ) ((adj.homEquiv _ _).symm u) ((adj.homEquiv _ _).symm φ)
    ?_ ?_ hker
  · rw [← adj.homEquiv_naturality_left_symm, hu, adj.homEquiv_naturality_right_symm]
  · rw [← adj.homEquiv_naturality_right_symm, hug, adj.homEquiv_naturality_left_symm]

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- `isIso_homEquiv_symm_of_extensions` for two degree-zero Yoneda extensions. -/
theorem isIso_homEquiv_symm_of_yonedaExtensions {ℬ : Type*} [Category ℬ] [Abelian ℬ]
    {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj : L ⊣ R) [L.IsLeftAdjoint] {A₁ A₃ : 𝒜} {B₁ B₃ : ℬ}
    (E : Abelian.YonedaExtension A₃ A₁ 0) (P : Abelian.YonedaExtension B₃ B₁ 0)
    (u : E.Z.left ⟶ R.obj P.Z.left) (κ : A₁ ⟶ R.obj B₁) (φ : A₃ ⟶ R.obj B₃)
    (hu : E.f ≫ u = κ ≫ R.map P.f) (hug : u ≫ R.map P.g = E.g ≫ φ)
    [Epi ((adj.homEquiv _ _).symm κ)] [IsIso ((adj.homEquiv _ _).symm φ)]
    (hker : ∀ {Z : ℬ} (z : Z ⟶ L.obj A₁), z ≫ (adj.homEquiv _ _).symm κ = 0 →
      z ≫ L.map E.f = 0) :
    IsIso ((adj.homEquiv _ _).symm u) :=
  isIso_homEquiv_symm_of_extensions adj _ (yonedaExtension_shortExact E) _
    (yonedaExtension_shortExact P) u κ φ hu hug hker

end Comparison

namespace FlatThickeningComplexSituation

variable (D : FlatThickeningComplexSituation i t)

omit [HasSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The induced map `I₂ ⟶ I₁` of defining ideals of the upper row is an epimorphism. -/
theorem epi_idealMap₂₁ : Epi D.upper.idealMap₂₁ :=
  D.upper_shortExact.choose_spec.epi_g

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- **`h^♯ : O'₂ ⟶ O'₁` is locally surjective.** -/
theorem isLocallySurjective_hSharp :
    Presheaf.IsLocallySurjective Y.J D.upper.lower.hSharp.hom := by
  classical
  have := D.epi_idealMap₂₁
  have hI := sheafModule_epi_locallySurjective D.upper.idealMap₂₁
  have h₂ := D.upper.lower.fSharp₂_locallySurjective
  let M := D.upper.lower
  constructor
  intro U r
  have hlift : ∀ {V : Y.C} (g : V ⟶ U), Presheaf.imageSieve M.fSharp₂.hom
      (i.fSharp.hom.app (Opposite.op U) r) g →
      ∃ a : M.O₂.obj.obj (Opposite.op V), M.fSharp₂.hom.app (Opposite.op V) a =
        (baseRing i).obj.map g.op (i.fSharp.hom.app (Opposite.op U) r) := fun g hg ↦ hg
  have hdiff : ∀ {V : Y.C} (g : V ⟶ U) (a : M.O₂.obj.obj (Opposite.op V)),
      M.fSharp₂.hom.app (Opposite.op V) a =
        (baseRing i).obj.map g.op (i.fSharp.hom.app (Opposite.op U) r) →
      ∃ c : M.first.I.val.obj (Opposite.op V), M.inclOne (Opposite.op V) c =
        Y.O.obj.map g.op r - M.hSharp.hom.app (Opposite.op V) a := by
    intro V g a ha
    refine M.first.exists_ideal_section (Opposite.op V) _ ?_
    rw [map_sub, M.fSharp_hSharp_apply, ha]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      i.fSharp.hom.naturality g.op, sub_self]
  refine Y.J.superset_covering ?_ (Y.J.bind_covering
    (Presheaf.imageSieve_mem Y.J M.fSharp₂.hom (i.fSharp.hom.app (Opposite.op U) r))
    (fun V g hg ↦ Presheaf.imageSieve_mem Y.J
      ((PresheafOfModules.toPresheaf _).map D.upper.idealMap₂₁.val)
      (hdiff g (hlift g hg).choose (hlift g hg).choose_spec).choose))
  rintro W _ ⟨V, k, g, hg, ⟨b, hb⟩, rfl⟩
  set a := (hlift g hg).choose with ha
  set c := (hdiff g a (hlift g hg).choose_spec).choose with hc
  have hcspec : M.inclOne (Opposite.op V) c = Y.O.obj.map g.op r -
      M.hSharp.hom.app (Opposite.op V) a :=
    (hdiff g a (hlift g hg).choose_spec).choose_spec
  change D.upper.idealMap₂₁.val.app (Opposite.op W) b = M.first.I.val.map k.op c at hb
  refine ⟨M.O₂.obj.map k.op a +
    (show M.O₂.obj.obj (Opposite.op W) from M.inclTwo (Opposite.op W) b), ?_⟩
  have h1 : M.hSharp.hom.app (Opposite.op W)
      (show M.O₂.obj.obj (Opposite.op W) from M.inclTwo (Opposite.op W) b) =
      Y.O.obj.map k.op (M.inclOne (Opposite.op V) c) :=
    (M.inclOne_idealMap (Opposite.op W) b).symm.trans
      ((congrArg (M.inclOne (Opposite.op W)) hb).trans (M.inclOne_naturality k.op c))
  have h2 : M.hSharp.hom.app (Opposite.op W) (M.O₂.obj.map k.op a) =
      Y.O.obj.map k.op (M.hSharp.hom.app (Opposite.op V) a) :=
    NatTrans.naturality_apply M.hSharp.hom k.op a
  calc M.hSharp.hom.app (Opposite.op W) (M.O₂.obj.map k.op a +
        (show M.O₂.obj.obj (Opposite.op W) from M.inclTwo (Opposite.op W) b))
      = Y.O.obj.map k.op (M.hSharp.hom.app (Opposite.op V) a) +
          Y.O.obj.map k.op (M.inclOne (Opposite.op V) c) := by
        rw [map_add, h1, h2]
    _ = Y.O.obj.map k.op (M.hSharp.hom.app (Opposite.op V) a +
          (show Y.O.obj.obj (Opposite.op V) from M.inclOne (Opposite.op V) c)) :=
        (map_add _ _ _).symm
    _ = Y.O.obj.map k.op (Y.O.obj.map g.op r) := by
        congr 1
        rw [show (show Y.O.obj.obj (Opposite.op V) from M.inclOne (Opposite.op V) c) =
          Y.O.obj.map g.op r - M.hSharp.hom.app (Opposite.op V) a from hcspec, add_sub_cancel]
    _ = Y.O.obj.map (k ≫ g).op r := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **The extension `0 ⟶ I₂ ⊗ ℱ ⟶ ℱ'₂ ⟶ ℱ ⟶ 0` of `O'₂`-modules attached to the flat lift
`ℱ'₂`**: its kernel term is the ideal product `I₂·ℱ'₂`, read as `I₂ ⊗_O ℱ` through the canonical
map of Stacks 08MQ, so its canonical action map is the identity. -/
noncomputable def secondExtension :
    Abelian.YonedaExtension ((structureRestrict D.i₂).obj D.F)
      ((structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.second.I)) 0 :=
  D.secondLift.fixedActionExtension D.i₂ D.t₂ D.f D.f₂ D.upper.lower.second D.lower.lower.second
    D.restrict₂ D.F D.isStrictPullbackIdealMap₂ D.isFlat_reducedBaseModule₂

/-- The canonical action map of the extension attached to `ℱ'₂` is the identity. -/
theorem secondExtension_actionMap :
    (extensionActionMap D.upper.lower.second D.secondExtension).1 = 𝟙 _ :=
  D.secondLift.extensionActionMap_fixedActionExtension D.i₂ D.t₂ D.f D.f₂ D.upper.lower.second
    D.lower.lower.second D.restrict₂ D.F D.isStrictPullbackIdealMap₂ D.isFlat_reducedBaseModule₂

/-- Multiplication by a section `b` of `I₂` on `ℱ'₂` is the inclusion of `b ⊗ x̄`. -/
theorem secondExtension_f_tmul (U : Y.Cᵒᵖ) (b : D.upper.lower.second.I.val.obj U)
    (x : D.secondExtension.Z.left.val.obj U) :
    D.secondExtension.f.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
          (PresheafOfModules.tensorObj D.upper.lower.second.I.val D.F.val)).app U
          (b ⊗ₜ[(baseRing i).obj.obj U] D.secondExtension.g.val.app U x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf D.upper.lower.O₂).obj.obj U from
        D.upper.lower.second.incl.val.app U b) • x := by
  have h := (extensionActionMap D.upper.lower.second D.secondExtension).2 U b x
  rwa [D.secondExtension_actionMap] at h

/-- The map `I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` of kernel modules induced by the morphism `h` of thickenings, read
over `O'₂`. -/
noncomputable abbrev kernelMap :
    (structureRestrict D.i₂).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        D.F).obj D.upper.lower.second.I) ⟶
      (structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        D.F).obj D.upper.lower.first.I) :=
  (structureRestrict D.i₂).map
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.upper.idealMap₂₁)

/-- The pushout of the extension attached to `ℱ'₂` along the map of kernel modules: a short
complex `0 ⟶ I₁ ⊗ ℱ ⟶ ℱ'₂ ⊔_{I₂ ⊗ ℱ} (I₁ ⊗ ℱ) ⟶ ℱ ⟶ 0` of `O'₂`-modules. -/
noncomputable abbrev pushoutComplex :=
  Abelian.pushoutShortComplex
    (ShortComplex.mk D.secondExtension.f D.secondExtension.g
      (yonedaExtension_comp_zero D.secondExtension)) D.kernelMap

/-- The pushout is short exact. -/
theorem pushoutComplex_shortExact : D.pushoutComplex.ShortExact :=
  Abelian.pushoutShortComplex_shortExact (yonedaExtension_shortExact D.secondExtension) _

/-- **The pushout is annihilated by the kernel of `h^♯ : O'₂ ⟶ O'₁`.** -/
theorem pushout_smul_eq_zero (U : Y.Cᵒᵖ) (a : D.upper.lower.O₂.obj.obj U)
    (ha : D.upper.lower.hSharp.hom.app U a = 0) (m : D.pushoutComplex.X₂.val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf D.upper.lower.O₂).obj.obj U from a) • m = 0 := by
  classical
  let E := D.secondExtension
  let K := (structureRestrict D.i₂).obj
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
      D.upper.lower.first.I)
  let inl := pushout.inl E.f D.kernelMap
  let inr := pushout.inr E.f D.kernelMap
  let q : E.Z.left ⊞ K ⟶ D.pushoutComplex.X₂ := biprod.desc inl inr
  have : Epi q := by
    constructor
    intro Z g₁ g₂ hg
    apply pushout.hom_ext
    · simpa only [q, biprod.inl_desc_assoc] using congrArg (biprod.inl ≫ ·) hg
    · simpa only [q, biprod.inr_desc_assoc] using congrArg (biprod.inr ≫ ·) hg
  have := sheafModule_epi_locallySurjective q
  refine smul_eq_zero_of_locallySurjective q U _ m fun V t x ↦ ?_
  let r : (Stacks.SheafOfModules.Tensor.ringSheaf D.upper.lower.O₂).obj.obj (Opposite.op V) :=
    D.upper.lower.O₂.obj.map t.op a
  have hr : D.upper.lower.hSharp.hom.app (Opposite.op V) r = 0 := by
    change D.upper.lower.hSharp.hom.app (Opposite.op V) (D.upper.lower.O₂.obj.map t.op a) = 0
    rw [NatTrans.naturality_apply, ha, map_zero]
  have hr₂ : D.upper.lower.fSharp₂.hom.app (Opposite.op V) r = 0 := by
    rw [← D.upper.lower.fSharp_hSharp_apply, hr, map_zero]
  have hq : q.val.app (Opposite.op V) x =
      inl.val.app (Opposite.op V) ((biprod.fst : E.Z.left ⊞ K ⟶ _).val.app (Opposite.op V) x) +
        inr.val.app (Opposite.op V) ((biprod.snd : E.Z.left ⊞ K ⟶ _).val.app (Opposite.op V) x) :=
    congrArg (fun φ : E.Z.left ⊞ K ⟶ D.pushoutComplex.X₂ ↦ φ.val.app (Opposite.op V) x)
      (biprod.desc_eq (f := inl) (g := inr))
  change r • q.val.app (Opposite.op V) x = 0
  have e : ∀ {A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf D.upper.lower.O₂)}
      (φ : A ⟶ D.pushoutComplex.X₂) (y : A.val.obj (Opposite.op V)),
      r • φ.val.app (Opposite.op V) y = φ.val.app (Opposite.op V) (r • y) :=
    fun φ y ↦ ((φ.val.app (Opposite.op V)).hom.map_smul _ _).symm
  rw [hq, smul_add, e inl, e inr]
  obtain ⟨b, hb⟩ := (D.upper.lower.second.kernel (Opposite.op V) r).1 hr₂
  have hk : r • (biprod.snd : E.Z.left ⊞ K ⟶ _).val.app (Opposite.op V) x = 0 := by
    change D.upper.lower.fSharp₂.hom.app (Opposite.op V) r •
      (show (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I).val.obj (Opposite.op V) from
          (biprod.snd : E.Z.left ⊞ K ⟶ _).val.app (Opposite.op V) x) = 0
    rw [hr₂, zero_smul]
  have hzero : D.upper.idealMap₂₁.val.app (Opposite.op V) b = 0 := by
    refine D.upper.lower.inclOne_injective (Opposite.op V)
      ((D.upper.lower.inclOne_idealMap (Opposite.op V) b).trans ?_)
    have hb' : D.upper.lower.second.incl.val.app (Opposite.op V) b = r := hb
    change D.upper.lower.hSharp.hom.app (Opposite.op V)
      (D.upper.lower.second.incl.val.app (Opposite.op V) b) = _
    rw [hb', hr]
    exact (map_zero (D.upper.lower.first.incl.val.app (Opposite.op V)).hom).symm
  have hy : inl.val.app (Opposite.op V)
      (r • (biprod.fst : E.Z.left ⊞ K ⟶ _).val.app (Opposite.op V) x) = 0 := by
    rw [← hb, ← D.secondExtension_f_tmul]
    change (E.f ≫ inl).val.app (Opposite.op V) _ = 0
    rw [pushout.condition]
    change inr.val.app (Opposite.op V) ((((Stacks.SheafOfModules.Tensor.sheafTensor
      (baseRing i)).flip.obj D.F).map D.upper.idealMap₂₁).val.app (Opposite.op V) _) = 0
    refine (congrArg (inr.val.app (Opposite.op V))
      (tensorSheaf_map_unit_tmul (baseRing i) D.upper.idealMap₂₁ (Opposite.op V) b _)).trans ?_
    rw [hzero]
    refine (congrArg (fun z ↦ inr.val.app (Opposite.op V)
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (PresheafOfModules.tensorObj D.upper.lower.first.I.val D.F.val)).app (Opposite.op V) z))
      (TensorProduct.zero_tmul _ _)).trans ?_
    exact (congrArg (inr.val.app (Opposite.op V)) (map_zero _)).trans (map_zero _)
  rw [hy, hk, map_zero, add_zero]

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- `h^♯ : O'₂ ⟶ O'₁` is locally surjective, on underlying sheaves of rings. -/
theorem isLocallySurjective_ringMapH :
    Presheaf.IsLocallySurjective Y.J D.upper.lower.ringMapH.hom := by
  change Presheaf.IsLocallySurjective Y.J
    (Functor.whiskerRight D.upper.lower.hSharp.hom (forget₂ CommRingCat RingCat))
  refine ⟨?_⟩
  intro U s
  simpa [Presheaf.imageSieve] using D.isLocallySurjective_hSharp.imageSieve_mem s

/-- Restriction of scalars along `h^♯ : O'₂ ⟶ O'₁` is fully faithful. -/
noncomputable def restrictScalarsHFullyFaithful :
    (SheafOfModules.restrictScalars D.upper.lower.ringMapH).FullyFaithful :=
  haveI : Presheaf.IsLocallySurjective Y.J D.upper.lower.ringMapH.hom :=
    D.isLocallySurjective_ringMapH
  haveI : Sheaf.IsLocallySurjective D.upper.lower.ringMapH :=
    ⟨D.isLocallySurjective_ringMapH.imageSieve_mem⟩
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective D.upper.lower.ringMapH

/-- The pushout, read with its outer terms restricted along `O'₂ ⟶ O'₁ ⟶ i_*O`. -/
noncomputable def pushoutExtension :
    Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars D.upper.lower.ringMapH).obj ((structureRestrict i).obj D.F))
      ((SheafOfModules.restrictScalars D.upper.lower.ringMapH).obj ((structureRestrict i).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.first.I))) 0 :=
  Abelian.shortExactYonedaExtension (S := ShortComplex.mk
      ((D.upper.lower.restrictHIso _).hom ≫ D.pushoutComplex.f)
      (D.pushoutComplex.g ≫ (D.upper.lower.restrictHIso D.F).inv)
      (by rw [Category.assoc, ← Category.assoc D.pushoutComplex.f, D.pushoutComplex.zero,
        zero_comp, comp_zero]))
    (ShortComplex.shortExact_of_iso (S₁ := D.pushoutComplex)
      (ShortComplex.isoMk (D.upper.lower.restrictHIso _).symm (Iso.refl _)
        (D.upper.lower.restrictHIso D.F).symm
        (by simp) (by simp)) D.pushoutComplex_shortExact)

/-- The middle term of the pushout is a restriction of scalars along `h^♯`. -/
theorem pushoutExtension_essImage :
    (SheafOfModules.restrictScalars D.upper.lower.ringMapH).essImage
      D.pushoutExtension.Z.left :=
  have : Presheaf.IsLocallySurjective Y.J D.upper.lower.ringMapH.hom :=
    D.isLocallySurjective_ringMapH
  essImage_restrictScalars_of_smul_eq_zero D.upper.lower.ringMapH _
    fun U a ha m ↦ D.pushout_smul_eq_zero U a ha m

/-- The descent of the pushout along `h^♯`, with its comparison to the pushout. -/
theorem exists_pulledExtension :
    ∃ (E : Abelian.YonedaExtension ((structureRestrict i).obj D.F)
        ((structureRestrict i).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.first.I)) 0)
      (e : (SheafOfModules.restrictScalars D.upper.lower.ringMapH).obj E.Z.left ≅
        D.pushoutExtension.Z.left),
      (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map E.f ≫ e.hom =
          D.pushoutExtension.f ∧
        e.hom ≫ D.pushoutExtension.g =
          (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map E.g := by
  have hex := restrictScalars_exact D.upper.lower.ringMapH
  have := hex.1
  have := hex.2
  exact Abelian.yonedaExtension_descend _ D.restrictScalarsHFullyFaithful _
    D.pushoutExtension_essImage

/-- The descent of the pushout along `h^♯`: an extension `0 ⟶ I₁ ⊗ ℱ ⟶ P ⟶ ℱ ⟶ 0` of
`O'₁`-modules. -/
noncomputable def pushoutDescent :
    Abelian.YonedaExtension ((structureRestrict i).obj D.F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        D.F).obj D.upper.lower.first.I)) 0 :=
  D.exists_pulledExtension.choose

/-- The comparison of the restriction of `pushoutDescent` along `h^♯` with the pushout. -/
noncomputable def pushoutDescentIso :
    (SheafOfModules.restrictScalars D.upper.lower.ringMapH).obj D.pushoutDescent.Z.left ≅
      D.pushoutComplex.X₂ :=
  D.exists_pulledExtension.choose_spec.choose

/-- Under `pushoutDescentIso`, the restriction of the first map of `pushoutDescent` along `h^♯`
is the first map of the pushout complex. -/
theorem pushoutDescentIso_f :
    (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map D.pushoutDescent.f ≫
        D.pushoutDescentIso.hom =
      (D.upper.lower.restrictHIso _).hom ≫ D.pushoutComplex.f :=
  D.exists_pulledExtension.choose_spec.choose_spec.1

/-- Under `pushoutDescentIso`, the second map of the pushout complex is the restriction of the
second map of `pushoutDescent` along `h^♯`. -/
theorem pushoutDescentIso_g :
    D.pushoutDescentIso.hom ≫ D.pushoutComplex.g ≫ (D.upper.lower.restrictHIso D.F).inv =
      (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map D.pushoutDescent.g :=
  D.exists_pulledExtension.choose_spec.choose_spec.2

/-- **The adjunction `h^* ⊣ h_*` of Stacks 03D7 for `h`**, with the direct image read as
restriction of scalars along `h^♯`
(`AlgebraicGeometry.RingedToposHom.coefficientMorphismPushforwardIso`). -/
noncomputable def adjH :
    pullbackModules D.h.toRingedToposModulesHom ⊣
      SheafOfModules.restrictScalars D.upper.lower.ringMapH :=
  D.h.pullbackAdjPushforwardModulesViaComparison.ofNatIsoRight
    (RingedToposHom.coefficientMorphismPushforwardIso D.upper.lower.hSharp).symm

/-- The map `I₃ ⊗ ℱ ⟶ I₂ ⊗ ℱ` of kernel modules, read over `O'₂`. -/
noncomputable abbrev kernelMap₃₂ :=
  (structureRestrict D.i₂).map
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.upper.idealMap₃₂)

/-- **For an extension `0 ⟶ I₂ ⊗ ℱ ⟶ E ⟶ ℱ ⟶ 0` over `O'₂` with identity action, the
composite `I₃ ⊗ ℱ ⟶ I₂ ⊗ ℱ ⟶ E ⟶ M` with any `O'₂`-linear map into an `O'₁`-module
vanishes.** -/
theorem kernelMap₃₂_comp_f_comp_eq_zero
    (E : Abelian.YonedaExtension ((structureRestrict D.i₂).obj D.F)
      ((structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.second.I)) 0)
    (hE : (extensionActionMap D.upper.lower.second E).1 = 𝟙 _)
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (φ : E.Z.left ⟶ (SheafOfModules.restrictScalars D.upper.lower.ringMapH).obj M) :
    D.kernelMap₃₂ ≫ E.f ≫ φ = 0 := by
  have : Epi E.g := E.epi_g
  let p : E.Z.left.val.presheaf ⟶ D.F.val.presheaf := (PresheafOfModules.toPresheaf _).map E.g.val
  have : Presheaf.IsLocallySurjective Y.J p := sheafModule_epi_locallySurjective E.g
  refine tensorSheaf_restrict_hom_ext_of_locallySurjective (baseRing i)
    ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map D.i₂.fSharp) p fun U c y ↦ ?_
  have hEf := (extensionActionMap D.upper.lower.second E).2 U (D.upper.idealMap₃₂.val.app U c) y
  rw [hE] at hEf
  have hc : D.upper.fSharp₃.hom.app U (D.upper.third.incl.val.app U c) = 0 :=
    (D.upper.third.kernel U _).2 ⟨c, rfl⟩
  have h0 : D.upper.lower.ringMapH.hom.app U
      (D.upper.lower.second.incl.val.app U (D.upper.idealMap₃₂.val.app U c)) = 0 := by
    have h := D.upper.upper.inclOne_idealMap U c
    change D.upper.lower.second.incl.val.app U (D.upper.idealMap₃₂.val.app U c) =
      D.upper.h₃₂.hom.app U (D.upper.third.incl.val.app U c) at h
    change D.upper.lower.hSharp.hom.app U
      (D.upper.lower.second.incl.val.app U (D.upper.idealMap₃₂.val.app U c)) = 0
    rw [h]
    exact D.upper.h₃₂_comp_hSharp_apply_eq_zero D.upper_isComplex U _ hc
  change φ.val.app U (E.f.val.app U
      ((((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₃₂).val.app U _)) = 0
  refine (congrArg (fun z ↦ φ.val.app U (E.f.val.app U z))
    (tensorSheaf_map_unit_tmul (baseRing i) D.upper.idealMap₃₂ U c (p.app U y))).trans ?_
  refine (congrArg (φ.val.app U) hEf).trans ?_
  refine ((φ.val.app U).hom.map_smul _ y).trans ?_
  change (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
      D.upper.lower.ringMapH.hom.app U
        (D.upper.lower.second.incl.val.app U (D.upper.idealMap₃₂.val.app U c))) •
    (show M.val.obj U from φ.val.app U y) = 0
  rw [h0, zero_smul]

/-- **The map `h^*ℱ'₂ ⟶ P`** adjoint to the inclusion of `ℱ'₂` into the pushout. -/
noncomputable def pulledToPushoutDescent : D.pulledModule ⟶ D.pushoutDescent.Z.left :=
  (D.adjH.homEquiv _ _).symm
    (pushout.inl D.secondExtension.f D.kernelMap ≫ D.pushoutDescentIso.inv)

end FlatThickeningComplexSituation

namespace MorphismOfFirstOrderThickenings

variable {i : RingedToposHom X Y} (M : MorphismOfFirstOrderThickenings i)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The identification of an `O`-module read along `O'₂ ⟶ O'₁ ⟶ i_*O` with it read along
`O'₂ ⟶ i_*O` is natural. -/
theorem restrictHIso_inv_naturality
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))} (φ : N ⟶ N') :
    (structureRestrict (reshapeHom i M.O₂ M.fSharp₂)).map φ ≫ (M.restrictHIso N').inv =
      (M.restrictHIso N).inv ≫
        (SheafOfModules.restrictScalars M.ringMapH).map ((structureRestrict i).map φ) := by
  ext U x
  rfl

end MorphismOfFirstOrderThickenings

namespace FlatThickeningComplexSituation

variable (D : FlatThickeningComplexSituation i t)

/-- The counit of `h^* ⊣ h_*` is an isomorphism. -/
instance isIso_adjH_counit : IsIso D.adjH.counit := by
  haveI := D.restrictScalarsHFullyFaithful.full
  haveI := D.restrictScalarsHFullyFaithful.faithful
  exact D.adjH.counit_isIso_of_R_fully_faithful

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The transpose of a restriction-of-scalars identification is an isomorphism. -/
theorem isIso_adjH_homEquiv_symm_restrictHIso_inv
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))) :
    IsIso ((D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso N).inv) := by
  rw [Adjunction.homEquiv_counit]
  infer_instance

omit [HasSheafify Y.J AddCommGrpCat.{w}] in
/-- The transpose of the map of kernel modules is `I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` after the identification
`h^*(I₂ ⊗ ℱ) = I₂ ⊗ ℱ`. -/
theorem adjH_homEquiv_symm_kernelMap :
    (D.adjH.homEquiv _ _).symm (D.kernelMap ≫ (D.upper.lower.restrictHIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I)).inv) =
      (D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.second.I)).inv ≫
        (structureRestrict i).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
            D.upper.idealMap₂₁) :=
    (congrArg (D.adjH.homEquiv _ _).symm
      (D.upper.lower.restrictHIso_inv_naturality _)).trans
      (D.adjH.homEquiv_naturality_right_symm _ _)

/-- `h^*` kills `I₃ ⊗ ℱ ⟶ I₂ ⊗ ℱ ⟶ ℱ'₂`. -/
theorem map_kernelMap₃₂_comp_map_f (E : Abelian.YonedaExtension ((structureRestrict D.i₂).obj D.F)
      ((structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.second.I)) 0)
    (hE : (extensionActionMap D.upper.lower.second E).1 = 𝟙 _) :
    (pullbackModules D.h.toRingedToposModulesHom).map D.kernelMap₃₂ ≫
      (pullbackModules D.h.toRingedToposModulesHom).map E.f = 0 := by
  have : (pullbackModules D.h.toRingedToposModulesHom).IsLeftAdjoint := D.adjH.isLeftAdjoint
  rw [← Functor.map_comp]
  have h := D.kernelMap₃₂_comp_f_comp_eq_zero E hE (D.adjH.unit.app E.Z.left)
  rw [← Category.assoc] at h
  exact Adjunction.map_eq_zero_of_comp_unit_eq_zero D.adjH _ h

omit [HasSheafify Y.J AddCommGrpCat.{w}] in
/-- The map `I₃ ⊗ ℱ ⟶ I₂ ⊗ ℱ` commutes with the identifications `h^*(Iₖ ⊗ ℱ) = Iₖ ⊗ ℱ`. -/
theorem map_kernelMap₃₂_comp_adjH_homEquiv_symm :
    (pullbackModules D.h.toRingedToposModulesHom).map D.kernelMap₃₂ ≫
      (D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.second.I)).inv =
      (D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.third.I)).inv ≫
        (structureRestrict i).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
            D.upper.idealMap₃₂) :=
    (D.adjH.homEquiv_naturality_left_symm _ _).symm.trans
      ((congrArg (D.adjH.homEquiv _ _).symm
        (D.upper.lower.restrictHIso_inv_naturality _)).trans
        (D.adjH.homEquiv_naturality_right_symm _ _))

/-- The sequence `0 ⟶ I₃ ⊗ ℱ ⟶ I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ ⟶ 0` read over `O'₁` is short exact. -/
theorem idealTensor_shortExact_restrict :
    (ShortComplex.mk ((structureRestrict i).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
          D.upper.idealMap₃₂))
      ((structureRestrict i).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
          D.upper.idealMap₂₁))
      (by rw [← Functor.map_comp, D.upper.idealTensor_comp_eq_zero D.upper_isComplex D.F,
        Functor.map_zero])).ShortExact := by
  have hex₁ := restrictScalars_exact ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)
  have := hex₁.1
  have := hex₁.2
  exact D.idealTensor_shortExact.map_of_exact (structureRestrict i)

/-- **The kernel of the comparison on kernel terms is killed in `h^*ℱ'₂`.** -/
theorem comp_map_f_eq_zero
    (E : Abelian.YonedaExtension ((structureRestrict D.i₂).obj D.F)
      ((structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.second.I)) 0)
    (hE : (extensionActionMap D.upper.lower.second E).1 = 𝟙 _)
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (z : Z ⟶ (pullbackModules D.h.toRingedToposModulesHom).obj
      ((structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.second.I)))
    (hz : (z ≫ (D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.second.I)).inv) ≫ (structureRestrict i).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
          D.upper.idealMap₂₁) = 0) :
    z ≫ (pullbackModules D.h.toRingedToposModulesHom).map E.f = 0 := by
  have hS := D.idealTensor_shortExact_restrict
  have := hS.mono_f
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hS.fIsKernel _ hz
  have := D.isIso_adjH_homEquiv_symm_restrictHIso_inv
  have hz' : z = l ≫ (structureRestrict i).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₃₂) ≫ inv ((D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
            D.upper.lower.second.I)).inv) := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv _).mpr hl.symm
  have h3 : (structureRestrict i).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₃₂) ≫ inv ((D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
            D.upper.lower.second.I)).inv) =
      inv ((D.adjH.homEquiv _ _).symm (D.upper.lower.restrictHIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.third.I)).inv) ≫
        (pullbackModules D.h.toRingedToposModulesHom).map D.kernelMap₃₂ := by
    rw [IsIso.comp_inv_eq, Category.assoc, D.map_kernelMap₃₂_comp_adjH_homEquiv_symm,
      IsIso.inv_hom_id_assoc]
  rw [hz', Category.assoc, Category.assoc, reassoc_of% h3, D.map_kernelMap₃₂_comp_map_f E hE,
    comp_zero, comp_zero]

/-- **A map out of `ℱ'₂` into an extension over `O'₁` compatible with `I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` and with
the projections to `ℱ` transposes to an isomorphism out of `h^*ℱ'₂`.** -/
theorem isIso_adjH_homEquiv_symm
    (E : Abelian.YonedaExtension ((structureRestrict D.i₂).obj D.F)
      ((structureRestrict D.i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          D.F).obj D.upper.lower.second.I)) 0)
    (hE : (extensionActionMap D.upper.lower.second E).1 = 𝟙 _)
    (P : Abelian.YonedaExtension ((structureRestrict i).obj D.F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        D.F).obj D.upper.lower.first.I)) 0)
    (u : E.Z.left ⟶ (SheafOfModules.restrictScalars D.upper.lower.ringMapH).obj P.Z.left)
    (hu : E.f ≫ u = D.kernelMap ≫ (D.upper.lower.restrictHIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I)).inv ≫
      (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map P.f)
    (hug : u ≫ (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map P.g =
      E.g ≫ (D.upper.lower.restrictHIso D.F).inv) :
    IsIso ((D.adjH.homEquiv _ _).symm u) := by
  have hK := D.idealTensor_shortExact
  have hex₂ := restrictScalars_exact
    ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map D.i₂.fSharp)
  have := hex₂.1
  have := hex₂.2
  have : (pullbackModules D.h.toRingedToposModulesHom).IsLeftAdjoint := D.adjH.isLeftAdjoint
  have : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
    D.upper.idealMap₂₁) := hK.epi_g
  have : Epi D.kernelMap := inferInstanceAs (Epi ((structureRestrict D.i₂).map
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
      D.upper.idealMap₂₁)))
  have := D.isIso_adjH_homEquiv_symm_restrictHIso_inv
  have : Epi ((D.adjH.homEquiv _ _).symm (D.kernelMap ≫ (D.upper.lower.restrictHIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I)).inv)) := by
    rw [D.adjH_homEquiv_symm_kernelMap]
    infer_instance
  exact isIso_homEquiv_symm_of_yonedaExtensions D.adjH E P u
    (D.kernelMap ≫ (D.upper.lower.restrictHIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I)).inv) (D.upper.lower.restrictHIso D.F).inv
    (hu.trans (Category.assoc _ _ _).symm) hug
    (fun z hz ↦ D.comp_map_f_eq_zero E hE z ((Category.assoc _ _ _).trans
      ((congrArg (z ≫ ·) D.adjH_homEquiv_symm_kernelMap.symm).trans hz)))

/-- The inclusion of `ℱ'₂` into the pushout restricts, on kernel terms, to `I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ`. -/
theorem f_comp_pushoutInclusion :
    D.secondExtension.f ≫ pushout.inl D.secondExtension.f D.kernelMap ≫ D.pushoutDescentIso.inv =
      D.kernelMap ≫ (D.upper.lower.restrictHIso
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.first.I)).inv ≫
        (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map D.pushoutDescent.f := by
  rw [(Iso.eq_comp_inv _).2 D.pushoutDescentIso_f, Category.assoc, Iso.inv_hom_id_assoc,
    pushout.condition_assoc]

/-- The inclusion of `ℱ'₂` into the pushout is compatible with the projections to `ℱ`. -/
theorem pushoutInclusion_comp_g :
    (pushout.inl D.secondExtension.f D.kernelMap ≫ D.pushoutDescentIso.inv) ≫
        (SheafOfModules.restrictScalars D.upper.lower.ringMapH).map D.pushoutDescent.g =
      D.secondExtension.g ≫ (D.upper.lower.restrictHIso D.F).inv := by
  rw [← D.pushoutDescentIso_g, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc]
  exact congrArg (· ≫ (D.upper.lower.restrictHIso D.F).inv)
    (Abelian.inl_pushoutShortComplex_g (ShortComplex.mk D.secondExtension.f D.secondExtension.g
      (yonedaExtension_comp_zero D.secondExtension)) D.kernelMap)

/-- **`h^*ℱ'₂` is the descended pushout**: the map `h^*ℱ'₂ ⟶ P` adjoint to the inclusion of
`ℱ'₂` into the pushout is an isomorphism. -/
instance isIso_pulledToPushoutDescent : IsIso D.pulledToPushoutDescent :=
  D.isIso_adjH_homEquiv_symm D.secondExtension D.secondExtension_actionMap D.pushoutDescent _
    D.f_comp_pushoutInclusion D.pushoutInclusion_comp_g

/-- The inclusion of `ℱ'₂` into the pushout, as a map into the descended pushout read over
`O'₂`. -/
noncomputable def pushoutInclusion :
    D.secondExtension.Z.left ⟶ (D.upper.lower.restrictedExtension D.pushoutDescent).Z.left :=
  pushout.inl D.secondExtension.f D.kernelMap ≫ D.pushoutDescentIso.inv

/-- The inclusion of `ℱ'₂` into the pushout is a map of extensions over `O'₂` restricting to
`I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` on kernel terms. -/
theorem f_comp_pushoutInclusion' :
    D.secondExtension.f ≫ D.pushoutInclusion =
      (structureRestrict D.i₂).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
            D.upper.idealMap₂₁) ≫
        (D.upper.lower.restrictedExtension D.pushoutDescent).f :=
  D.f_comp_pushoutInclusion

/-- The inclusion of `ℱ'₂` into the pushout is compatible with the projections to `ℱ`. -/
theorem pushoutInclusion_comp_g' :
    D.pushoutInclusion ≫ (D.upper.lower.restrictedExtension D.pushoutDescent).g =
      D.secondExtension.g := by
  change (pushout.inl D.secondExtension.f D.kernelMap ≫ D.pushoutDescentIso.inv) ≫
      ((SheafOfModules.restrictScalars D.upper.lower.ringMapH).map D.pushoutDescent.g ≫
        (D.upper.lower.restrictHIso D.F).hom) = _
  rw [← Category.assoc, D.pushoutInclusion_comp_g, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **The canonical action of `I₁` on the descended pushout is the identity.** -/
theorem pushoutDescent_actionMap :
    (extensionActionMap D.upper.lower.first D.pushoutDescent).1 = 𝟙 _ := by
  have hnat := (extensionActionMap_comp_of_hom D.upper.lower.second D.secondExtension
    (D.upper.lower.restrictedExtension D.pushoutDescent)
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
      D.upper.idealMap₂₁) D.pushoutInclusion D.f_comp_pushoutInclusion'
      D.pushoutInclusion_comp_g').trans
    (D.upper.lower.restrictedExtension_actionMap D.pushoutDescent)
  rw [D.secondExtension_actionMap, Category.id_comp] at hnat
  have : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
      D.upper.idealMap₂₁) := D.idealTensor_shortExact.epi_g
  refine ((cancel_epi (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
      D.upper.idealMap₂₁)).mp ?_).symm
  exact (Category.comp_id _).trans hnat

end FlatThickeningComplexSituation

end Deformation.ToposThickening

end
