module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackInclusionNotExact

/-!
# The image of a map of coherent modules on a stack need not be coherent

**Stacks 0GR9** part (2), and **Stacks 0GQL** part (2) before it, assert that the image of a map
`φ : 𝓕 ⟶ 𝓖` of coherent (respectively quasi-coherent) modules on an algebraic stack, *computed in
`Mod(𝒪_𝒳)`*, is again coherent (respectively quasi-coherent).  That is false, already for
`𝒳 = Spec ℤ`, `𝓕 = 𝓖 = 𝒪` and `φ = 2`: on the big fppf site the image `I = 2𝒪 ⊆ 𝒪` vanishes on
every scheme over `𝔽₂`, while `I(Spec ℤ) = 2ℤ ≅ ℤ`, so `I` is not cartesian and hence not
quasi-coherent.

This file proves the general mechanism.  If `𝒪 --π--> I --ι--> 𝒪` factors `2` with `π` epi and
`ι` mono, and `g : y ⟶ x` is a morphism between objects over affine schemes such that `2` is a
nonzerodivisor on `𝒪(x)`, the kernel of `𝒪(x) ⟶ 𝒪(y)` is `2𝒪(x)`, and `𝒪(y)` is a nonzero ring in
which `2 = 0`, then `I` is not quasi-coherent:

* `I(y) = 0`, since every section of `I` over `y` is locally `π(f)`, and `ι(π f) = 2f = 0`;
* so `ι(t)` restricts to `0` on `y` for every `t ∈ I(x)`, whence `ι(t) ∈ 2𝒪(x)`, and `t ↦ ι(t)/2`
  is an `𝒪(x)`-linear form on `I(x)` sending `π(1)` to `1`;
* a quasi-coherent module is cartesian between affine objects
  (`AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite`), so
  `𝒪(y) ⊗_{𝒪(x)} I(x) ≅ I(y) = 0`; but the linear form base-changes to a map to `𝒪(y)` sending
  `1 ⊗ π(1)` to `1 ≠ 0`.

## Main results

* `AlgebraicGeometry.Stack.sections_eq_zero_of_factor_two`: the vanishing `I(y) = 0`.
* `AlgebraicGeometry.Stack.not_isQuasicoherentOnSite_of_factor_two`: `I` is not quasi-coherent.
* `AlgebraicGeometry.Stack.not_isCoherent_abelianImage_two` and
  `AlgebraicGeometry.Stack.not_isCoherent_image_two`: on the stack of `Spec ℤ`
  (`AlgebraicGeometry.Stack.specIntStack`, locally Noetherian by
  `AlgebraicGeometry.Stack.specIntStack_isLocallyNoetherian`), the image of `2 : 𝒪 ⟶ 𝒪` is not
  coherent, in either construction of the image.
* `AlgebraicGeometry.Stack.exists_not_isCoherent_image_of_isCoherent`: **the literal Stacks 0GR9
  part (2) is false**, for every big fppf site.

## Implementation notes

The corrected form of the clause, proved elsewhere, is about the image of `φ` *in* `Coh(𝒪_𝒳)`,
which is `Q(Im φ)` for the coherator `Q` of Stacks 0778; the argument above shows that `Im φ`
computed in `Mod(𝒪_𝒳)` differs from it: their difference is the parasitic module `Ker(π)`-type
discrepancy invisible on flat objects, here concentrated over `𝔽₂`.  No `@[stacks]` attribute is
placed here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.AssociatedModuleNotExact
  (specInt contains_specInt contains_specFTwo intToFTwo)

universe u v w

namespace AlgebraicGeometry.Stack

section General

/-- If `π ≫ ι` is multiplication by `2`, then `ι (π t) = t + t` on sections. -/
private theorem app_comp_eq_add_self {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}
    {I : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    {π : SheafOfModules.unit _ ⟶ I} {ι : I ⟶ SheafOfModules.unit _} (hπι : π ≫ ι = 𝟙 _ + 𝟙 _)
    (z : 𝒳ᵒᵖ) (t : (SheafOfModules.unit _).val.obj z) :
    ι.val.app z (π.val.app z t) = t + t := by
  have := congrArg (fun f => f t)
    (congrArg ConcreteCategory.hom (congrArg (fun φ => φ.val.app z) hπι))
  simp only [SheafOfModules.add_val, PresheafOfModules.add_app, PresheafOfModules.comp_app,
    ModuleCat.hom_add, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.hom_id,
    ModuleCat.hom_comp, SheafOfModules.comp_val] at this
  exact this

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  [HasSheafify (associatedTopology B S hS p B.topology) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p B.topology).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The middle term of a factorization of `2` vanishes where `2` does.**  If
`𝒪 --π--> I --ι--> 𝒪` factors multiplication by `2` with `π` an epimorphism and `ι` a
monomorphism, then `I` has no nonzero section over an object on which `2 = 0`. -/
theorem sections_eq_zero_of_factor_two
    {I : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (π : SheafOfModules.unit _ ⟶ I) (ι : I ⟶ SheafOfModules.unit _) [Epi π] [Mono ι]
    (hπι : π ≫ ι = 𝟙 _ + 𝟙 _) {y : 𝒳} (h2 : (2 : fibredSectionRing B S hS p y) = 0)
    (σ : I.val.obj (op y)) : σ = 0 := by
  have hinj : Function.Injective (ι.val.app (op y)) :=
    PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map ι) (op y)
  refine hinj ((?_ : ι.val.app (op y) σ = 0).trans (map_zero _).symm)
  obtain ⟨T, hT, hloc⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi π σ
  refine ((Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget
    (SheafOfModules.unit (ringStructureSheafCore B S hS p hp B.topology le_rfl))) T
    hT).isSeparatedFor.ext (t₁ := ι.val.app (op y) σ) (t₂ := 0) ?_
  intro W g hg
  obtain ⟨t, ht⟩ := hloc g hg
  have h2W : (2 : fibredSectionRing B S hS p W) = 0 := by
    have := congrArg (fibredSectionRestrict (B := B) (S := S) (hS := hS) (p := p) g) h2
    rwa [map_ofNat, map_zero] at this
  have h0 : (SheafOfModules.unit _).val.map g.op (0 : (SheafOfModules.unit
      (ringStructureSheafCore B S hS p hp B.topology le_rfl)).val.obj (op y)) = 0 := map_zero _
  refine ((PresheafOfModules.naturality_apply ι.val g.op σ).symm.trans ?_).trans h0.symm
  have ht' : π.val.app (op W) t = I.val.map g.op σ := ht
  let t' : fibredSectionRing B S hS p W := t
  have h2t : (2 : fibredSectionRing B S hS p W) * t' = 0 := by rw [h2W, zero_mul]
  rw [← ht']
  exact (app_comp_eq_add_self hπι (op W) t').trans ((two_mul t').symm.trans h2t)

/-- **A factorization of `2` through an epimorphism followed by a monomorphism is not
quasi-coherent**, as soon as there is a morphism `g : y ⟶ x` between objects over affine schemes
along which `2` is a nonzerodivisor upstairs, the kernel of restriction is `2𝒪(x)`, and `𝒪(y)` is
a nonzero ring of characteristic `2`. -/
theorem not_isQuasicoherentOnSite_of_factor_two
    {I : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (π : SheafOfModules.unit _ ⟶ I) (ι : I ⟶ SheafOfModules.unit _) [Epi π] [Mono ι]
    (hπι : π ≫ ι = 𝟙 _ + 𝟙 _) {x y : 𝒳} (g : y ⟶ x)
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (h2 : (2 : fibredSectionRing B S hS p y) = 0) (h10 : (1 : fibredSectionRing B S hS p y) ≠ 0)
    (hker : ∀ a : fibredSectionRing B S hS p x, fibredSectionRestrict g a = 0 → ∃ c, a = 2 * c)
    (hnzd : ∀ c : fibredSectionRing B S hS p x, 2 * c = 0 → c = 0) :
    ¬ I.IsQuasicoherentOnSite := by
  intro hI
  have hcart := isCartesianBetweenAffines_of_isQuasicoherentOnSite hp I hI g hx hy
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
  let := fibredSectionsModule hp I x
  -- `ι` on sections over `x`, read as a map to the functions on `x`
  let ιx : I.val.obj (op x) → fibredSectionRing B S hS p x := fun t => ι.val.app (op x) t
  have hιx_add : ∀ a b, ιx (a + b) = ιx a + ιx b := fun a b => map_add _ a b
  have hιx_smul : ∀ (c : fibredSectionRing B S hS p x) a, ιx (c • a) = c * ιx a :=
    fun c a => (ι.val.app (op x)).hom.map_smul c a
  have hI0 : ∀ σ : I.val.obj (op y), σ = 0 := sections_eq_zero_of_factor_two hp π ι hπι h2
  -- every `ι t` restricts to zero on `y`
  have hres : ∀ t, fibredSectionRestrict g (ιx t) = 0 := by
    intro t
    exact (PresheafOfModules.naturality_apply ι.val g.op t).symm.trans
      ((congrArg (ι.val.app (op y)) (hI0 _)).trans (map_zero _))
  -- so `ι t = 2 lam(t)` for a unique `lam(t)`
  choose lamf hlamf using fun t => hker (ιx t) (hres t)
  have hlam_unique : ∀ t c, ιx t = 2 * c → lamf t = c := fun t c hc =>
    sub_eq_zero.1 (hnzd _ (by rw [mul_sub, ← hlamf t, ← hc, sub_self]))
  let laml : I.val.obj (op x) →ₗ[fibredSectionRing B S hS p x] fibredSectionRing B S hS p x :=
    { toFun := lamf
      map_add' := fun a b => hlam_unique _ _ (by rw [hιx_add, hlamf a, hlamf b, mul_add])
      map_smul' := fun c a => hlam_unique _ _ (by
        rw [hιx_smul, hlamf a, RingHom.id_apply, smul_eq_mul]; ring) }
  -- the section `s = π(1)` has `ι s = 2`, so `lam s = 1`
  let s : I.val.obj (op x) := π.val.app (op x) (1 : fibredSectionRing B S hS p x)
  have hs : ιx s = 2 :=
    (app_comp_eq_add_self hπι (op x) (1 : fibredSectionRing B S hS p x)).trans
      (one_add_one_eq_two (R := fibredSectionRing B S hS p x))
  have hlams : laml s = 1 := hlam_unique _ _ (by rw [hs, mul_one])
  -- `1 ⊗ s` vanishes, the base change comparison being injective with zero target
  have hz : ((1 : fibredSectionRing B S hS p y) ⊗ₜ[fibredSectionRing B S hS p x] s :
      TensorProduct (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
        (I.val.obj (op x))) = 0 :=
    hcart.1 ((hI0 _).trans (hI0 _).symm)
  -- but the linear form base-changes to a map sending `1 ⊗ s` to `1`
  let ψ := TensorProduct.lift ((LinearMap.mul (fibredSectionRing B S hS p x)
    (fibredSectionRing B S hS p y)).compl₂
      ((Algebra.linearMap (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)).comp laml))
  have hψ := congrArg ψ hz
  rw [map_zero] at hψ
  exact h10 (by simpa only [ψ, TensorProduct.lift.tmul, LinearMap.compl₂_apply,
    LinearMap.mul_apply', LinearMap.comp_apply, Algebra.linearMap_apply, hlams, map_one,
    one_mul] using hψ)

end General

/-! ### The stack of `Spec ℤ` -/

section SpecInt

variable (B : BigFppfSite.{u})

/-- The stack of `Spec ℤ` is locally Noetherian: the identity is a smooth surjective scheme atlas
and `Spec ℤ` is Noetherian. -/
theorem specIntStack_isLocallyNoetherian :
    HasPropertyOnSomeSchemeAtlas B specInt.{u} (contains_specInt B)
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) (specIntStack.{u, u} B) := by
  refine ⟨specIntOver B, 𝟙 _, isSurjective_id _ _ _ _, AlgebraicStacks.isSmooth_id _ _ _ _, ?_⟩
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- The terminal object of the stack of `Spec ℤ`, lying over `Spec ℤ`. -/
noncomputable abbrev specIntTop : (specIntStack.{u, u} B).val.val.obj := Over.mk (𝟙 (specIntOver B))

/-- The point `Spec 𝔽₂ ⟶ Spec ℤ`, as a morphism of the big fppf site. -/
noncomputable abbrev specFTwoMap :
    B.obj (contains_specFTwo B) ⟶ B.obj (contains_specInt B) :=
  ObjectProperty.homMk AssociatedModuleNotExact.specFTwoOver.{u}

/-- `Spec 𝔽₂` as a scheme over `Spec ℤ`. -/
noncomputable abbrev specFTwoOver : BigFppfOver B specInt.{u} (contains_specInt B) :=
  Over.mk (specFTwoMap B)

/-- `Spec 𝔽₂` as an object of the stack of `Spec ℤ`. -/
noncomputable abbrev specFTwoPt : (specIntStack.{u, u} B).val.val.obj :=
  Over.mk (Over.homMk (specFTwoMap B) (by simp) : specFTwoOver B ⟶ specIntOver B)

/-- The point `Spec 𝔽₂ ⟶ Spec ℤ`, as a morphism of the stack of `Spec ℤ`. -/
noncomputable abbrev specFTwoToTop : specFTwoPt B ⟶ specIntTop B :=
  Over.homMk (Over.homMk (specFTwoMap B) (by simp)) (by ext; simp)

end SpecInt

/-! ### The counterexample -/

section Counterexample

variable (B : BigFppfSite.{u})

/-- The structure sheaf of the stack of `Spec ℤ`. -/
noncomputable abbrev specIntRingSheaf :=
  ringStructureSheafCore B specInt.{u} (contains_specInt B)
    (specIntStack.{u, u} B).val.val.p (specIntStack.{u, u} B).val.isFiberedInGroupoids B.topology
    le_rfl

/-- The category of objects of the stack of `Spec ℤ` is essentially small. -/
instance essentiallySmall_specIntStack : EssentiallySmall.{u} (specIntStack.{u, u} B).val.val.obj :=
  essentiallySmall_obj_algebraicStack _ _ _ _

/-- Sheafification of presheaves of abelian groups exists for the associated topology on the stack
of `Spec ℤ`. -/
instance hasSheafify_specIntStack : HasSheafify (associatedTopology B specInt.{u}
    (contains_specInt B) (specIntStack.{u, u} B).val.val.p B.topology) AddCommGrpCat.{u} :=
  hasSheafifyAddCommGrpCat_associatedTopology _ _ _ _ _

/-- For the associated topology on the stack of `Spec ℤ`, a morphism of presheaves of abelian
groups becomes an isomorphism after sheafification exactly when it is locally bijective. -/
instance wEqualsLocallyBijective_specIntStack : (associatedTopology B specInt.{u}
    (contains_specInt B) (specIntStack.{u, u} B).val.val.p B.topology).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_associatedTopology _ _ _ _ _

/-- Multiplication by `2` on the structure sheaf of the stack of `Spec ℤ`. -/
noncomputable abbrev twoMap : SheafOfModules.unit (specIntRingSheaf B) ⟶
    SheafOfModules.unit (specIntRingSheaf B) :=
  𝟙 _ + 𝟙 _

/-- The ring of functions on `Spec ℤ` is `ℤ`. -/
noncomputable abbrev specIntRingEquiv :
    fibredSectionRing B specInt.{u} (contains_specInt B) (specIntStack.{u, u} B).val.val.p
      (specIntTop B) ≃+* ULift.{u} ℤ :=
  (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv

/-- The ring of functions on `Spec 𝔽₂` is `𝔽₂`. -/
noncomputable abbrev specFTwoRingEquiv :
    fibredSectionRing B specInt.{u} (contains_specInt B) (specIntStack.{u, u} B).val.val.p
      (specFTwoPt B) ≃+* ULift.{u} (ZMod 2) :=
  (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (ZMod 2)))).commRingCatIsoToRingEquiv

/-- Restricting a global function on `Spec ℤ` to `Spec 𝔽₂` corresponds, under the identifications
`specIntRingEquiv` and `specFTwoRingEquiv`, to reduction `ℤ → 𝔽₂`. -/
theorem specFTwoRingEquiv_restrict (a : fibredSectionRing B specInt.{u}
    (contains_specInt B) (specIntStack.{u, u} B).val.val.p (specIntTop B)) :
    specFTwoRingEquiv B (fibredSectionRestrict (specFTwoToTop B) a) =
      intToFTwo (specIntRingEquiv B a) :=
  congrArg (fun f => f a) (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_naturality intToFTwo.{u}))

/-- The four arithmetic side conditions of
`AlgebraicGeometry.Stack.not_isQuasicoherentOnSite_of_factor_two` at `Spec 𝔽₂ ⟶ Spec ℤ`. -/
theorem specInt_sideConditions :
    (2 : fibredSectionRing B _ _ (specIntStack.{u, u} B).val.val.p (specFTwoPt B)) = 0 ∧
    (1 : fibredSectionRing B _ _ (specIntStack.{u, u} B).val.val.p (specFTwoPt B)) ≠ 0 ∧
    (∀ a : fibredSectionRing B _ _ (specIntStack.{u, u} B).val.val.p (specIntTop B),
      fibredSectionRestrict (specFTwoToTop B) a = 0 → ∃ c, a = 2 * c) ∧
    (∀ c : fibredSectionRing B _ _ (specIntStack.{u, u} B).val.val.p (specIntTop B),
      2 * c = 0 → c = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (specFTwoRingEquiv B).injective
    rw [map_ofNat, map_zero]
    exact congrArg ULift.up (by decide : (2 : ZMod 2) = 0)
  · intro h
    have := congrArg (specFTwoRingEquiv B) h
    rw [map_one, map_zero] at this
    exact absurd (congrArg ULift.down this) (by decide)
  · intro a ha
    have h0 : intToFTwo (specIntRingEquiv B a) = 0 := by
      rw [← specFTwoRingEquiv_restrict, ha, map_zero]
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ (specIntRingEquiv B a).down :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 (congrArg ULift.down h0)
    refine ⟨(specIntRingEquiv B).symm ⟨k⟩, (specIntRingEquiv B).injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, map_ofNat]
    exact ULift.ext _ _ (by simpa using hk)
  · intro c hc
    apply (specIntRingEquiv B).injective
    have := congrArg (fun z => (specIntRingEquiv B z).down) hc
    simp only [map_mul, map_ofNat, map_zero] at this
    exact ULift.ext _ _ (by simpa using this)

/-- The scheme underlying the terminal object `specIntTop` is affine. -/
theorem isAffine_specIntTop : IsAffine (((specIntStack.{u, u} B).val.val.p ⋙
    BigFppfOver.toScheme B _ _).obj (specIntTop B)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- The scheme underlying `specFTwoPt` is affine. -/
theorem isAffine_specFTwoPt : IsAffine (((specIntStack.{u, u} B).val.val.p ⋙
    BigFppfOver.toScheme B _ _).obj (specFTwoPt B)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (ULift.{u} (ZMod 2)))))

/-- **The image of `2 : 𝒪 ⟶ 𝒪` on the stack of `Spec ℤ`, formed as in an abelian category, is not
quasi-coherent.** -/
theorem not_isQuasicoherentOnSite_abelianImage_two :
    ¬ (Abelian.image (twoMap B)).IsQuasicoherentOnSite :=
  have h := specInt_sideConditions B
  not_isQuasicoherentOnSite_of_factor_two (specIntStack.{u, u} B).val.isFiberedInGroupoids
    (Abelian.factorThruImage _) (Abelian.image.ι _) (Abelian.image.fac _) (specFTwoToTop B)
    (isAffine_specIntTop B) (isAffine_specFTwoPt B) h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **The image of `2 : 𝒪 ⟶ 𝒪` on the stack of `Spec ℤ`, formed as
`CategoryTheory.Limits.image`, is not quasi-coherent.** -/
theorem not_isQuasicoherentOnSite_image_two :
    ¬ (Limits.image (twoMap B)).IsQuasicoherentOnSite :=
  have h := specInt_sideConditions B
  not_isQuasicoherentOnSite_of_factor_two (specIntStack.{u, u} B).val.isFiberedInGroupoids
    (factorThruImage _) (Limits.image.ι _) (image.fac _) (specFTwoToTop B)
    (isAffine_specIntTop B) (isAffine_specFTwoPt B) h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **The image of a map of coherent modules, computed in `Mod(𝒪_𝒳)`, need not be coherent**:
the counterexample to the literal **Stacks 0GR9** part (2).  On the locally Noetherian algebraic
stack of `Spec ℤ` (`AlgebraicGeometry.Stack.specIntStack_isLocallyNoetherian`) the structure sheaf
is coherent (`AlgebraicGeometry.Stack.isCoherent_unit`) and the image of multiplication by `2` on
it is not. -/
theorem not_isCoherent_abelianImage_two :
    ¬ IsCoherent B _ _ (specIntStack.{u, u} B) (Abelian.image (twoMap B)) :=
  fun h => not_isQuasicoherentOnSite_abelianImage_two B h.1.1

/-- The same, for the image formed as `CategoryTheory.Limits.image`. -/
theorem not_isCoherent_image_two :
    ¬ IsCoherent B _ _ (specIntStack.{u, u} B) (Limits.image (twoMap B)) :=
  fun h => not_isQuasicoherentOnSite_image_two B h.1.1

/-- **Stacks 0GR9 part (2) fails as literally stated.**  There are a locally Noetherian algebraic
stack and a map of coherent modules on it whose image computed in `Mod(𝒪_𝒳)` is not coherent. -/
theorem exists_not_isCoherent_image_of_isCoherent :
    ∃ (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, u} B S hS)
      (_ : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
      (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl)) (φ : F ⟶ G),
      IsCoherent B S hS 𝒳 F ∧ IsCoherent B S hS 𝒳 G ∧
        ¬ IsCoherent B S hS 𝒳 (Abelian.image φ) ∧ ¬ IsCoherent B S hS 𝒳 (Limits.image φ) :=
  ⟨_, _, specIntStack.{u, u} B, specIntStack_isLocallyNoetherian B, _, _, twoMap B,
    isCoherent_unit B _ _ _ (specIntStack_isLocallyNoetherian B),
    isCoherent_unit B _ _ _ (specIntStack_isLocallyNoetherian B),
    not_isCoherent_abelianImage_two B, not_isCoherent_image_two B⟩

end Counterexample

end AlgebraicGeometry.Stack

end
