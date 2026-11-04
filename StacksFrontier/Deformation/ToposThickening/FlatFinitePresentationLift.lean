module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationOfReduction
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ModulesAbelian

/-!
# Finite presentation across a first order thickening of ringed topoi

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi (Stacks 08MB),
with square-zero ideal `I = Ker(i^♯) ⊂ O'`, let `ℱ'` be an `O'`-module and set `ℱ = i^*ℱ'`.
This file proves that `ℱ'` is of finite presentation as soon as `ℱ` is, provided relations among
sections of `ℱ'` with coefficients in `I` vanish trivially
(`Deformation.ToposThickening.ReductionPresentation.IdealRelationsVanish`). That proviso holds
when `ℱ'` is flat over a sheaf of rings `A ⟶ O'` whose image generates `I` locally
(`Deformation.ToposThickening.ReductionPresentation.idealRelationsVanish_of_isFlat`), which is the
situation of Stacks 08VU.

## Main results

* `Deformation.ToposThickening.FirstOrderThickening.isFinitePresentation_pushforward`: finite
  presentation of an `O`-module moves to its direct image, as an `i_*O`-module on the site of the
  target (Stacks 03DM along the equivalence `(Sh(C), O) ⟶ (Sh(D), i_*O)`).
* `Deformation.ToposThickening.FirstOrderThickening.kernelIsIdealProduct`: the kernel of the
  reduction `ℱ' ⟶ i_*i^*ℱ'` is locally the ideal product, on sections (Stacks 08MP).
* `Deformation.ToposThickening.idealRelationsVanish_of_mono`: relations with coefficients in the
  ideal vanish trivially as soon as `I ⊗ ℱ' ⟶ ℱ'` is injective.
* `Deformation.ToposThickening.isFinitePresentation_of_isFinitePresentation_pullbackModules`: the
  implication `i^*ℱ'` of finite presentation `⇒` `ℱ'` of finite presentation.

Stacks 08VU itself, with its hypotheses of flatness and strictness, is
`Deformation.ToposThickening.isFinitePresentation_iff_pullbackModules_of_isStrict`.

## How the proof goes

Everything is moved to the site of `D`, as the source's proof does with "we may and do assume
`C = C'`". The reduction `ℱ = i^*ℱ'` is read there as the `i_*O`-module `𝒢 = i_*ℱ`, and the unit
`q : ℱ' ⟶ i_*i^*ℱ'` is the reduction map: it is surjective with kernel `I·ℱ'` by the ideal-product
sequence of Stacks 08MP. Finite presentation of `ℱ` transports to `𝒢` along the equivalence of
ringed topoi `(Sh(C), O) ⟶ (Sh(D), i_*O)` (Stacks 03DM). Then
`Deformation.ToposThickening.ReductionPresentation.isFinitePresentation_of_reduction` applies.

## References

* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.SheafOfModules.FlatSquareZero (ringMap)
open Deformation.ToposThickening.ReductionPresentation

universe v u v' u' w

namespace Deformation.ToposThickening

section Ambient

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The site of the target of `i`, carrying the direct image `i_*O` of the structure sheaf of the
source. -/
noncomputable abbrev ambientRingedTopos (i : RingedToposHom X X') : RingedTopos.{v', u', w} :=
  { C := X'.C, J := X'.J, O := (pushforwardCommRingFunctor i.toToposHom).obj X.O }

/-- `i`, read as a morphism to `ambientRingedTopos i`; its structure map is the identity. -/
noncomputable def toAmbient (i : RingedToposHom X X') :
    RingedToposHom X (ambientRingedTopos i) where
  toToposHom := i.toToposHom
  fSharp := 𝟙 _

/-- The structure map of `toAmbient i` is the identity, hence an isomorphism. -/
instance (i : RingedToposHom X X') : IsIso (toAmbient i).fSharp :=
  inferInstanceAs (IsIso (𝟙 _))

/-- For a first order thickening, `toAmbient i` is a closed immersion of ringed topoi with
invertible structure map. -/
noncomputable def FirstOrderThickening.ambientClosedRingedImmersion {i : RingedToposHom X X'}
    (hi : FirstOrderThickening i) : ClosedRingedImmersion.{v, u, v', u', w} where
  source := X
  target := ambientRingedTopos i
  hom := toAmbient i
  isClosedImmersion := hi.isClosedImmersion
  structureMap_surjective := by
    change Sheaf.IsLocallySurjective ((ambientRingedTopos i).forgetRing.map (𝟙 _))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X'.C, HasWeakSheafify (X'.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X'.C, (X'.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **Finite presentation moves to the site of the target of a thickening.** If `ℳ` is an
`O`-module of finite presentation, then its direct image `i_*ℳ`, as an `i_*O`-module, is of
finite presentation: the direct image along `toAmbient i` is an equivalence, so `ℳ` is the
pullback of `i_*ℳ` along it, and finite presentation is intrinsic (Stacks 03DM). -/
theorem FirstOrderThickening.isFinitePresentation_pushforward {i : RingedToposHom X X'}
    (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : M.IsFinitePresentation) :
    ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
      M).IsFinitePresentation := by
  have : (toAmbient i).toToposHom.pushforward.IsEquivalence := hi.equiv
  have : HasWeakSheafify hi.ambientClosedRingedImmersion.source.J AddCommGrpCat.{w} :=
    inferInstanceAs (HasWeakSheafify X.J AddCommGrpCat.{w})
  have : hi.ambientClosedRingedImmersion.source.J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    inferInstanceAs (X.J.WEqualsLocallyBijective AddCommGrpCat.{w})
  have : (toAmbient i).pushforwardModules.IsEquivalence :=
    isEquivalence_pushforwardModules_of_isIso_fSharp hi.ambientClosedRingedImmersion
      (CategoryTheory.Functor.map_isIso (ambientRingedTopos i).forgetRing (𝟙 _))
  let adj := (toAmbient i).pullbackAdjPushforwardModules
  refine ((toAmbient i).isFinitePresentation_iff_pullbackModules
    ((toAmbient i).pushforwardModules.obj M)).2 ?_
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (asIso (adj.counit.app M)).symm hM

end Ambient


section KernelProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O R : Sheaf J CommRingCat.{w}}

/-- The objectwise submodule of `ℱ'` spanned by the products `a • m` with `a` killed by `π`. -/
noncomputable def kernelProductSubmodule (π : O ⟶ R)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) : F'.val.Submodule where
  obj U := Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U)
    { x | ∃ (a : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U))
      (m : ToType (F'.val.obj U)), ringMapApp π U a = 0 ∧ a • m = x }
  map {U V} f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, m, ha, rfl⟩
    refine Submodule.subset_span ⟨(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map f a,
      F'.val.map f m, ?_, (F'.val.map_smul f a m).symm⟩
    have := ringMapApp_resR π f.unop a
    rw [ha, Stacks.SheafOfModules.resR_zero] at this
    exact this

/-- A section of `kernelProductSubmodule π F'` is a finite sum `∑ cᵣ • yᵣ` with every
coefficient `cᵣ` in the kernel of `π`. -/
lemma exists_sum_of_mem_kernelProductSubmodule {π : O ⟶ R}
    {F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {U : Cᵒᵖ}
    {x : ToType (F'.val.obj U)} (hx : x ∈ (kernelProductSubmodule π F').obj U) :
    ∃ (N : ℕ) (c : Fin N → ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U))
      (y : Fin N → ToType (F'.val.obj U)), (∀ r, ringMapApp π U (c r) = 0) ∧
        x = ∑ r, c r • y r := by
  obtain ⟨N, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  choose a m ha hg using fun r => (g r).2
  refine ⟨N, fun r => f r * a r, m, fun r => by rw [map_mul, ha r, mul_zero], ?_⟩
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hg r, smul_smul]

end KernelProduct

section TensorMono

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O R : Sheaf J CommRingCat.{w}}

/-- The value of a map `ι : I ⟶ O` of `O`-modules on a section, read in the structure sheaf. -/
noncomputable abbrev unitHomApp {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (ii : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (b : ToType (I.val.obj U)) : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U) :=
  ii.val.app U b

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- `unitHomApp ii U` is linear over the sections of the structure sheaf. -/
lemma unitHomApp_smul {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (ii : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (c : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U)) (b : ToType (I.val.obj U)) :
    unitHomApp ii U (c • b) = c * unitHomApp ii U b :=
  (ii.val.app U).hom.map_smul c b

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- `unitHomApp ii U` commutes with finite sums. -/
lemma unitHomApp_sum {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (ii : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ) {n : ℕ}
    (b : Fin n → ToType (I.val.obj U)) :
    unitHomApp ii U (∑ k, b k) = ∑ k, unitHomApp ii U (b k) :=
  map_sum (ii.val.app U).hom.toAddMonoidHom _ _

open Stacks.SheafOfModules.FlatSquareZero (multiplicationMap multiplicationMap_tmul) in
/-- **Relations with coefficients in the ideal vanish trivially when `I ⊗_O ℱ' ⟶ ℱ'` is
injective.** A relation `∑ dₖ eₖ = 0` with `dₖ ∈ I` is the image of `∑ dₖ ⊗ eₖ`, which then
vanishes in the sheaf `I ⊗ ℱ'`, hence locally in the presheaf tensor product, where the equational
criterion for the vanishing of a tensor applies. -/
theorem idealRelationsVanish_of_mono {π : O ⟶ R}
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (ii : (SheafOfModules.restrictScalars (ringMap π)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hker : ∀ (U : Cᵒᵖ) (a : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U)),
      ringMapApp π U a = 0 → ∃ b, unitHomApp ii U b = a)
    (hii : ∀ (U : Cᵒᵖ) b, ringMapApp π U (unitHomApp ii U b) = 0)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hmono : Mono (multiplicationMap π I F' ii)) :
    IdealRelationsVanish π F' := by
  classical
  intro U n d e hd hde
  choose b hb using fun k => hker (op U) (d k) (hd k)
  let IU := ((SheafOfModules.restrictScalars (ringMap π)).obj I).val
  let P := PresheafOfModules.Monoidal.tensorObj IU F'.val
  let ξ : ToType (P.obj (op U)) := ∑ k, (b k : ToType (IU.obj (op U))) ⊗ₜ[O.obj.obj (op U)] e k
  let η := (PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app P
  let m := (multiplicationMap π I F' ii).val.app (op U)
  let φ : ToType (P.obj (op U)) →+ ToType (F'.val.obj (op U)) :=
    AddMonoidHom.mk' (fun x => m (η.app (op U) x)) fun x y =>
      (congrArg m ((η.app (op U)).hom.map_add x y)).trans (m.hom.map_add _ _)
  have hmult : m (η.app (op U) ξ) = 0 := by
    have e1 : m (η.app (op U) ξ) = ∑ k, m (η.app (op U)
        ((b k : ToType (IU.obj (op U))) ⊗ₜ[O.obj.obj (op U)] e k)) :=
      map_sum φ _ _
    rw [e1, ← hde]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hb k]
    exact multiplicationMap_tmul π I F' ii (op U) (b k) (e k)
  have hinj : Function.Injective m := Stacks.SheafOfModules.injective_val_app_of_mono _ _
  have hη0 : η.app (op U) ξ = η.app (op U) 0 := by
    apply hinj
    rw [hmult]
    have h0 : η.app (op U) (0 : ToType (P.obj (op U))) = 0 := LinearMap.map_zero _
    rw [h0]
    exact (LinearMap.map_zero _).symm
  have hloc : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map η) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf))
  refine ⟨_, Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map η) ξ 0 hη0,
    fun W f hf => ?_⟩
  have hW : ∑ k, Stacks.SheafOfModules.res ((SheafOfModules.restrictScalars (ringMap π)).obj I)
      f (b k) ⊗ₜ[O.obj.obj (op W)] Stacks.SheafOfModules.res F' f (e k) = 0 := by
    have hf' : P.map f.op ξ = P.map f.op 0 := hf
    rw [LinearMap.map_zero] at hf'
    exact (map_sum (P.map f.op).hom.toAddMonoidHom _ _).symm.trans hf'
  obtain ⟨n', P', t, c, u', A, h1, h2, h3⟩ :=
    Stacks.SheafOfModules.exists_relationPresentation_of_sum_tmul_eq_zero _ _ hW
  refine ⟨n', P', t, c, A, fun p => unitHomApp ii (op W) (u' p), fun p => hii _ _, h1, h2,
    fun j => ?_⟩
  have := congrArg (unitHomApp ii (op W)) (h3 j)
  rw [unitHomApp_sum, unitHomApp_sum] at this
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (this.trans
    (Finset.sum_congr rfl fun p _ => unitHomApp_smul ii (op W) (A j p) (u' p)))
  refine Eq.trans ?_ (unitHomApp_smul ii (op W) (c k j) _).symm
  congr 1
  rw [← hb k]
  exact (PresheafOfModules.naturality_apply ii.val f.op (b k)).symm

end TensorMono

section Lift

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X X'}

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The kernel of the structure map of a first order thickening is square zero, on sections. -/
lemma FirstOrderThickening.squareZeroKernel (hi : FirstOrderThickening i) :
    SquareZeroKernel i.fSharp := by
  intro U a b ha hb
  obtain ⟨α, hα⟩ := hi.exists_ideal_section U a ha
  obtain ⟨β, hβ⟩ := hi.exists_ideal_section U b hb
  rw [← hα, ← hβ]
  exact hi.square_zero U α β

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The ring map of a first order thickening is locally surjective. -/
lemma FirstOrderThickening.isLocallySurjective_ringMap (hi : FirstOrderThickening i) :
    Presheaf.IsLocallySurjective X'.J (ringMap i.fSharp).hom :=
  ⟨fun {_} x => hi.surjective.imageSieve_mem x⟩

private lemma exists_preimage_of_exact {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {R : Sheaf J RingCat.{w}} {A B D : SheafOfModules.{w} R} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) [Mono f] (hexact : (ShortComplex.mk f g hfg).Exact) (U : Cᵒᵖ)
    (x : ToType (B.val.obj U)) (hx : g.val.app U x = 0) :
    ∃ y : ToType (A.val.obj U), f.val.app U y = x := by
  let S := ShortComplex.mk f g hfg
  have hfork : IsLimit (KernelFork.ofι f hfg) :=
    (S.exact_and_mono_f_iff_f_is_kernel.mp ⟨hexact, inferInstance⟩).some
  let e := SheafOfModules.evaluation R U
  have : e.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hEval' : IsLimit ((KernelFork.ofι f hfg).map e) :=
    KernelFork.isLimitMapConeEquiv (KernelFork.ofι f hfg) e (isLimitOfPreserves e hfork)
  let xmap : ModuleCat.of (R.obj.obj U) (R.obj.obj U) ⟶ e.obj B :=
    ModuleCat.ofHom (LinearMap.smulRight LinearMap.id x)
  have hx1 : xmap 1 = x := by
    change ((LinearMap.id : (R.obj.obj U) →ₗ[R.obj.obj U] (R.obj.obj U)) 1) • x = x
    simp
  have hxmap : xmap ≫ e.map g = 0 := by
    ext
    rw [ModuleCat.comp_apply, hx1]
    exact hx
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hEval' xmap hxmap
  refine ⟨l 1, ?_⟩
  simp only [KernelFork.map_ι, KernelFork.ι_ofι] at hl
  have h := congrArg (fun q => q 1) hl
  rw [ModuleCat.comp_apply, hx1] at h
  exact h

/-- **The kernel of the reduction map is locally the ideal product**, on sections: this is the
ideal-product sequence of Stacks 08MP read on sections. -/
theorem FirstOrderThickening.kernelIsIdealProduct (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) :
    KernelIsIdealProduct (O := X'.O) (R := (pushforwardCommRingFunctor i.toToposHom).obj X.O)
      (π := i.fSharp)
      (G := ((pushforwardModuleFunctor i.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          i.toRingedToposModulesHom).obj F') : SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O))))
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') := by
  intro U x hx
  have hS := idealProductShortComplex_shortExact hi F'
  have : Mono (idealProductSubmodule hi F').ι := hS.mono_f
  obtain ⟨y, rfl⟩ := exists_preimage_of_exact _ _ _ hS.exact (op U) x hx
  have hle : idealProductSubmodule hi F' ≤
      Stacks.SheafOfModules.Submodule.sheafify (kernelProductSubmodule i.fSharp F') := by
    refine sInf_le fun V a m => ?_
    refine Stacks.PresheafOfModules.Submodule.le_sheafify _ _
      (Submodule.subset_span ⟨_, m, ?_, rfl⟩)
    exact (hi.kernel V _).2 ⟨a, rfl⟩
  have hy := SheafOfModules.Submodule.le_iff.1 hle _ y.2
  obtain ⟨S, hS, hmem⟩ := Stacks.PresheafOfModules.Submodule.mem_sheafify_iff.1 hy
  refine ⟨S, hS, fun V f hf => ?_⟩
  exact exists_sum_of_mem_kernelProductSubmodule (hmem f hf)


variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X'.C, HasWeakSheafify (X'.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X'.C, (X'.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 08VU, (2) ⇒ (1), for a single thickening.** Let `i` be a first order thickening of
ringed topoi and let `ℱ'` be an `O'`-module in which relations with coefficients in the
square-zero ideal `I` vanish trivially. If `i^*ℱ'` is of finite presentation, so is `ℱ'`. -/
theorem isFinitePresentation_of_isFinitePresentation_pullbackModules (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (hvan : IdealRelationsVanish i.fSharp F')
    (hF : ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom).obj F').IsFinitePresentation) :
    F'.IsFinitePresentation := by
  have : ∀ U : X'.C, HasSheafify (X'.J.over U) AddCommGrpCat.{w} := fun _ =>
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : HasSheafify X'.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hS := idealProductShortComplex_shortExact hi F'
  have hepi : Epi (i.pullbackAdjPushforwardModulesViaComparison.unit.app F') := hS.epi_g
  have hq := (Stacks.Sheaves.LocalGeneration.module_epi_iff_locallySurjective
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app F')).1 hepi
  exact isFinitePresentation_of_reduction (O := X'.O)
    (R := (pushforwardCommRingFunctor i.toToposHom).obj X.O) (π := i.fSharp)
    hi.isLocallySurjective_ringMap hi.squareZeroKernel hq (hi.kernelIsIdealProduct F') hvan
    (hi.isFinitePresentation_pushforward _ hF)

end Lift

end Deformation.ToposThickening

end
