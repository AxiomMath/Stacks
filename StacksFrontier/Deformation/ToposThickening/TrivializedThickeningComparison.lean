module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.TrivialExtensionClass

/-!
# Comparing the extension classes of two trivialized first order thickenings

Let `(Sh(C), O)` be a ringed topos and let `(Sh(D), O'₁)` and `(Sh(D), O'₂)` be two first order
thickenings of it presented on one site `D`, so that the two structure maps `s₁ : O'₁ ⟶ ι_*O`
and `s₂ : O'₂ ⟶ ι_*O` are taken along one and the same morphism of topoi `ι`. Let
`h^♯ : O'₂ ⟶ O'₁` be a morphism of thickenings over the base, that is, a map of structure
sheaves with `h^♯ ≫ s₁ = s₂`, and let `π₁`, `π₂` be trivializations of the two thickenings which
are compatible with `h`, in the sense that the splitting `σ₁ : O ⟶ O'₁` supplied by `π₁` is the
splitting `σ₂ : O ⟶ O'₂` supplied by `π₂` followed by `h^♯`. This is the condition
`π₁ = π₂ ∘ h` of the source, read on structure sheaves.

Let `F`, `K₁`, `K₂` be `O`-modules and `κ : K₂ ⟶ K₁` a map. An extension `F'₂` of `F` by `K₂`
over the second thickening and an extension `F'₁` of `F` by `K₁` over the first, together with a
map `F'₂ ⟶ F'₁` of `O'₂`-modules inducing `κ` on the kernels and the identity on `F` — which is
in particular what the pushout construction carrying `F'₂` to `F'₁` supplies — have extension
classes related by

```
  ξ_{F'₁} = ξ_{F'₂} ∘ κ    in Ext¹_O(F, K₁),
```

the right-hand side being the image of `ξ_{F'₂}` under the map `Ext¹_O(F, K₂) ⟶ Ext¹_O(F, K₁)`
given by functoriality of `Ext` in `κ`. This is the commutative square of Stacks 08MK.

## Main definitions

* `Deformation.ToposThickening.ringedToposOn`: the ringed topos carried by a sheaf of
  commutative rings on a fixed site.
* `Deformation.ToposThickening.homOn`: a morphism of ringed topoi into such a ringed topos.
* `Deformation.ToposThickening.structureRingHom`: the structure map of a thickening, read as a
  map of the underlying sheaves of rings.
* `Stacks.SheafOfModules.restrictScalarsCompIso`: restriction of scalars along a composite of
  maps of sheaves of rings is the composite of the two restrictions.

## Main results

* `Deformation.ToposThickening.underlyingExtensionClass_eq_comp_mk₀`: **Stacks 08MK**, the
  commutative square relating the two extension classes.

## References

* [Stacks Project, Tag 08MK](https://stacks.math.columbia.edu/tag/08MK)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe e v u w v' u' w' vv uu ww

namespace Stacks.SheafOfModules

section CompRestriction

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}
  {R₁ R₂ R₃ : Sheaf J RingCat.{ww}}

/-- **Restriction of scalars along a composite.** If `gf = f ≫ g` then restricting an
`R₃`-module to `R₁` along `gf` is restricting it to `R₂` along `g` and then to `R₁` along `f`. -/
noncomputable def restrictScalarsCompIso (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) (gf : R₁ ⟶ R₃)
    (h : gf = f ≫ g) (M : SheafOfModules.{ww} R₃) :
    (SheafOfModules.restrictScalars gf).obj M ≅
      (SheafOfModules.restrictScalars f).obj ((SheafOfModules.restrictScalars g).obj M) := by
  let e (U : Cᵒᵖ) :
      ((SheafOfModules.restrictScalars gf).obj M).val.obj U ≅
        ((SheafOfModules.restrictScalars f).obj
          ((SheafOfModules.restrictScalars g).obj M)).val.obj U := by
    have hU : (gf.hom.app U).hom = ((g.hom.app U).hom).comp ((f.hom.app U).hom) := by
      simpa using congrArg (fun q ↦ (q.hom.app U).hom) h
    exact ModuleCat.restrictScalarsComp'App _ _ _ hU (M.val.obj U)
  refine ⟨⟨{ app U := (e U).hom, naturality := ?_ }⟩, ⟨{ app U := (e U).inv, naturality := ?_ }⟩,
    ?_, ?_⟩
  · intro U V a
    ext x
    exact rfl
  · intro U V a
    ext x
    exact rfl
  all_goals
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact rfl

/-- The identification of restriction along a composite with the composite of the restrictions
is the identity on sections. -/
@[simp]
theorem restrictScalarsCompIso_hom_val_app (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) (gf : R₁ ⟶ R₃)
    (h : gf = f ≫ g) (M : SheafOfModules.{ww} R₃) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars gf).obj M).val.obj U) :
    (restrictScalarsCompIso f g gf h M).hom.val.app U x = x := rfl

/-- The inverse of the identification of restriction along a composite with the composite of the
restrictions is the identity on sections. -/
@[simp]
theorem restrictScalarsCompIso_inv_val_app (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) (gf : R₁ ⟶ R₃)
    (h : gf = f ≫ g) (M : SheafOfModules.{ww} R₃) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars f).obj
      ((SheafOfModules.restrictScalars g).obj M)).val.obj U) :
    (restrictScalarsCompIso f g gf h M).inv.val.app U x = x := rfl

/-- The inverse of the identification of a module with its restriction of scalars along a split
pair of ring maps is the identity on sections. -/
@[simp]
theorem restrictScalarsSplitIso_inv_val_app {R R' : Sheaf J RingCat.{ww}} (β : R ⟶ R')
    (α : R' ⟶ R) (h : β ≫ α = 𝟙 R) (M : SheafOfModules.{ww} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (restrictScalarsSplitIso β α h M).inv.val.app U x = x := rfl

end CompRestriction

end Stacks.SheafOfModules

namespace Deformation.ToposThickening

section OneSite

variable {D : Type u'} [Category.{v'} D]

/-- The ringed topos carried by a sheaf of commutative rings on a fixed site. -/
abbrev ringedToposOn (K : GrothendieckTopology D) (O : Sheaf K CommRingCat.{w'}) :
    RingedTopos.{v', u', w'} where
  C := D
  J := K
  O := O

variable {X : RingedTopos.{v, u, w}} {K : GrothendieckTopology D}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget RingCat.{w'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- A morphism of ringed topoi onto the ringed topos carried by a sheaf of commutative rings on
a fixed site, assembled from a morphism of topoi and a map of structure sheaves. -/
abbrev homOn (ι : MorphismOfTopoi X.Topos (Sheaf K (Type w')))
    {O : Sheaf K CommRingCat.{w'}} (s : O ⟶ (pushforwardCommRingFunctor ι).obj X.O) :
    RingedToposHom X (ringedToposOn K O) where
  toToposHom := ι
  fSharp := s

/-- The structure map of a thickening presented on a fixed site, read as a map of the underlying
sheaves of rings. -/
noncomputable abbrev structureRingHom {ι : MorphismOfTopoi X.Topos (Sheaf K (Type w'))}
    {O : Sheaf K CommRingCat.{w'}} (s : O ⟶ (pushforwardCommRingFunctor ι).obj X.O) :
    Stacks.SheafOfModules.Tensor.ringSheaf O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O) :=
  (sheafCompose K (forget₂ CommRingCat.{w'} RingCat.{w'})).map s

section Comparison

variable {ι : MorphismOfTopoi X.Topos (Sheaf K (Type w'))} {O₁ O₂ : Sheaf K CommRingCat.{w'}}
  (s₁ : O₁ ⟶ (pushforwardCommRingFunctor ι).obj X.O)
  (s₂ : O₂ ⟶ (pushforwardCommRingFunctor ι).obj X.O)

/-- A morphism of thickenings over the base, read as a map of the underlying sheaves of rings. -/
noncomputable abbrev morphismRingHom (h : O₂ ⟶ O₁) :
    Stacks.SheafOfModules.Tensor.ringSheaf O₂ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₁ :=
  (sheafCompose K (forget₂ CommRingCat.{w'} RingCat.{w'})).map h

/-- The two presentations of a module on the base agree: reading an `O`-module as an
`O'₂`-module along the structure map of the second thickening is reading it as an `O'₁`-module
and then as an `O'₂`-module along `h^♯`. -/
noncomputable def presentationCompIso (h : O₂ ⟶ O₁) (hh : h ≫ s₁ = s₂)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O))) :
    (SheafOfModules.restrictScalars (structureRingHom s₂)).obj M ≅
      (SheafOfModules.restrictScalars (morphismRingHom h)).obj
        ((SheafOfModules.restrictScalars (structureRingHom s₁)).obj M) :=
  Stacks.SheafOfModules.restrictScalarsCompIso _ _ _
    ((congrArg (sheafCompose K (forget₂ CommRingCat.{w'} RingCat.{w'})).map hh).symm.trans
      ((sheafCompose K (forget₂ CommRingCat.{w'} RingCat.{w'})).map_comp h s₁)) M

variable (hi₁ : FirstOrderThickening (homOn ι s₁)) (hi₂ : FirstOrderThickening (homOn ι s₂))
  (π₁ : Trivialization (homOn ι s₁)) (π₂ : Trivialization (homOn ι s₂))

/-- Reading an `O'₁`-module as an `O`-module along the splitting supplied by the trivialization
of the first thickening is reading it as an `O'₂`-module along `h^♯` and then as an `O`-module
along the splitting supplied by the trivialization of the second, when the two trivializations
are compatible with `h`. -/
noncomputable def splittingCompIso (h : O₂ ⟶ O₁)
    (hπ : splittingRingHom (homOn ι s₁) hi₁ π₁ =
      splittingRingHom (homOn ι s₂) hi₂ π₂ ≫ morphismRingHom h)
    (N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :
    (splitRestriction (homOn ι s₂) hi₂ π₂).obj
        ((SheafOfModules.restrictScalars (morphismRingHom h)).obj N) ≅
      (splitRestriction (homOn ι s₁) hi₁ π₁).obj N :=
  (Stacks.SheafOfModules.restrictScalarsCompIso _ _ _ hπ N).symm

/-- The comparison of the splittings is natural in the `O'₁`-module. -/
@[reassoc]
theorem splittingCompIso_naturality (h : O₂ ⟶ O₁)
    (hπ : splittingRingHom (homOn ι s₁) hi₁ π₁ =
      splittingRingHom (homOn ι s₂) hi₂ π₂ ≫ morphismRingHom h)
    {N N' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)} (ψ : N ⟶ N') :
    (splitRestriction (homOn ι s₂) hi₂ π₂).map
          ((SheafOfModules.restrictScalars (morphismRingHom h)).map ψ) ≫
        (splittingCompIso s₁ s₂ hi₁ hi₂ π₁ π₂ h hπ N').hom =
      (splittingCompIso s₁ s₂ hi₁ hi₂ π₁ π₂ h hπ N).hom ≫
        (splitRestriction (homOn ι s₁) hi₁ π₁).map ψ := rfl

/-- Identifying a module on the base with its double restriction of scalars is natural. -/
@[reassoc]
theorem splitRestrictionRestrictScalarsIso_naturality
    {O : Sheaf K CommRingCat.{w'}} (s : O ⟶ (pushforwardCommRingFunctor ι).obj X.O)
    (hi : FirstOrderThickening (homOn ι s)) (π : Trivialization (homOn ι s))
    {M M' : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O))}
    (ψ : M ⟶ M') :
    (splitRestriction (homOn ι s) hi π).map
          ((SheafOfModules.restrictScalars (structureRingHom s)).map ψ) ≫
        (splitRestrictionRestrictScalarsIso (homOn ι s) hi π M').hom =
      (splitRestrictionRestrictScalarsIso (homOn ι s) hi π M).hom ≫ ψ := rfl

/-- The comparison of the two presentations of a module on the base, read along the splitting of
the second trivialization and then compared with the splitting of the first, is the comparison of
the two double restrictions. -/
@[reassoc]
theorem splitRestriction_presentationCompIso (h : O₂ ⟶ O₁) (hh : h ≫ s₁ = s₂)
    (hπ : splittingRingHom (homOn ι s₁) hi₁ π₁ =
      splittingRingHom (homOn ι s₂) hi₂ π₂ ≫ morphismRingHom h)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O))) :
    (splitRestriction (homOn ι s₂) hi₂ π₂).map (presentationCompIso s₁ s₂ h hh M).hom ≫
        (splittingCompIso s₁ s₂ hi₁ hi₂ π₁ π₂ h hπ
          ((SheafOfModules.restrictScalars (structureRingHom s₁)).obj M)).hom =
      (splitRestrictionRestrictScalarsIso (homOn ι s₂) hi₂ π₂ M).hom ≫
        (splitRestrictionRestrictScalarsIso (homOn ι s₁) hi₁ π₁ M).inv := rfl

/-- The comparison of the two presentations, read along the splitting of the second
trivialization and then identified with the module on the base through the first trivialization,
is the identification through the second trivialization. -/
@[reassoc]
theorem splitRestriction_presentationCompIso_comp (h : O₂ ⟶ O₁) (hh : h ≫ s₁ = s₂)
    (hπ : splittingRingHom (homOn ι s₁) hi₁ π₁ =
      splittingRingHom (homOn ι s₂) hi₂ π₂ ≫ morphismRingHom h)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O))) :
    (splitRestriction (homOn ι s₂) hi₂ π₂).map (presentationCompIso s₁ s₂ h hh M).hom ≫
        (splittingCompIso s₁ s₂ hi₁ hi₂ π₁ π₂ h hπ
            ((SheafOfModules.restrictScalars (structureRingHom s₁)).obj M)).hom ≫
          (splitRestrictionRestrictScalarsIso (homOn ι s₁) hi₁ π₁ M).hom =
      (splitRestrictionRestrictScalarsIso (homOn ι s₂) hi₂ π₂ M).hom := rfl

section Classes

variable [HasWeakSheafify K AddCommGrpCat.{w'}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasSheafify K AddCommGrpCat.{w'}]

/-- If `h` is a morphism of trivialized first order thickenings of `(Sh(C), O)` and an extension
`F'₂` of `F` by `K₂` over the second thickening maps to an extension `F'₁` of `F` by `K₁` over
the first, inducing `κ : K₂ ⟶ K₁` on the kernels and the identity on `F`, then the class
`ξ_{F'₁}` is the image of `ξ_{F'₂}` under the map `Ext¹_O(F, K₂) ⟶ Ext¹_O(F, K₁)` given by
functoriality of `Ext` in `κ`. -/
@[stacks 08MK "the commutative square: the extension class of the image extension is the image
of the extension class under functoriality of `Ext` in the map of kernel modules"]
theorem underlyingExtensionClass_eq_comp_mk₀
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O)))]
    (h : O₂ ⟶ O₁) (hh : h ≫ s₁ = s₂)
    (hπ : splittingRingHom (homOn ι s₁) hi₁ π₁ =
      splittingRingHom (homOn ι s₂) hi₂ π₂ ≫ morphismRingHom h)
    (F K₁ K₂ : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor ι).obj X.O)))
    (κ : K₂ ⟶ K₁)
    (E₂ : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars (structureRingHom s₂)).obj F)
      ((SheafOfModules.restrictScalars (structureRingHom s₂)).obj K₂) 0)
    (E₁ : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars (structureRingHom s₁)).obj F)
      ((SheafOfModules.restrictScalars (structureRingHom s₁)).obj K₁) 0)
    (φ : E₂.Z.left ⟶
      (SheafOfModules.restrictScalars (morphismRingHom h)).obj E₁.Z.left)
    (hφf : E₂.f ≫ φ = (SheafOfModules.restrictScalars (structureRingHom s₂)).map κ ≫
      (presentationCompIso s₁ s₂ h hh K₁).hom ≫
        (SheafOfModules.restrictScalars (morphismRingHom h)).map E₁.f)
    (hφg : φ ≫ (SheafOfModules.restrictScalars (morphismRingHom h)).map E₁.g =
      E₂.g ≫ (presentationCompIso s₁ s₂ h hh F).hom) :
    underlyingExtensionClass (homOn ι s₁) hi₁ π₁ F K₁ E₁ =
      (underlyingExtensionClass (homOn ι s₂) hi₂ π₂ F K₂ E₂).comp
        (Abelian.Ext.mk₀ κ) (add_zero 1) := by
  let Ψ : splitExtension (homOn ι s₂) hi₂ π₂ F K₂ E₂ ⟶
      splitExtension (homOn ι s₁) hi₁ π₁ F K₁ E₁ :=
    { τ₁ := κ
      τ₂ := (splitRestriction (homOn ι s₂) hi₂ π₂).map φ ≫
        (splittingCompIso s₁ s₂ hi₁ hi₂ π₁ π₂ h hπ E₁.Z.left).hom
      τ₃ := 𝟙 F
      comm₁₂ := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        ext x
        exact (congrArg (fun q ↦ (q.val.app U).hom x) hφf).symm
      comm₂₃ := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        ext x
        exact congrArg (fun q ↦ (q.val.app U).hom x) hφg }
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (splitExtension_shortExact (homOn ι s₂) hi₂ π₂ F K₂ E₂)
    (splitExtension_shortExact (homOn ι s₁) hi₁ π₁ F K₁ E₁) Ψ
  simp only [Ψ] at hnat
  exact (Abelian.Ext.mk₀_id_comp _).symm.trans hnat.symm

end Classes

end Comparison

end OneSite

end Deformation.ToposThickening

end
