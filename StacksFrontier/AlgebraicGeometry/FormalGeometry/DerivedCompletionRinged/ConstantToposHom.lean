module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposTerminalSections
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# The morphism of ringed topoi with constant coefficients induced by a morphism of topoi

Let `Λ` be a commutative ring and let `f : Sh(𝒟) ⟶ Sh(𝒞)` be a morphism of topoi. Writing `Λ̲`
for the constant sheaf of rings on either site, `f` underlies a canonical morphism of ringed
topoi `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)`: its structure map `Λ̲ ⟶ f_*Λ̲` is the map of `Λ`-algebras,
determined by the requirement that the global section `a̲` of `Λ̲` on `𝒞` attached to `a ∈ Λ`
goes to the direct image of the global section `a̲` on `𝒟`. This is the morphism of ringed topoi
through which the source reads `Rf_*` and `Lf^*` on `D(𝒞, Λ)` and `D(𝒟, Λ)` in the setting of
[Stacks, Tag 099N].

## Main definitions

* `AlgebraicGeometry.RingedTopos.constant`: the ringed topos `(Sh(𝒞), Λ̲)`; the ringed site it
  presents is `AlgebraicGeometry.RingedSite.constant`, by `rfl`.
* `AlgebraicGeometry.RingedTopos.constantSectionHom`: the global section `a̲` of `Λ̲`, as a
  morphism out of the terminal sheaf of sets.
* `MorphismOfTopoi.constantRingedToposHom`: the morphism of ringed topoi
  `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)` underlain by `f`.

## Main results

* `MorphismOfTopoi.fSharp_app_constantSectionRingHom`: the structure map carries `a̲` to the
  direct image of `a̲`.
* `MorphismOfTopoi.map_constantSectionHom_comp_fSharpInverseImageRing`: in inverse-image form,
  the structure map `f⁻¹Λ̲ ⟶ Λ̲` carries the inverse image of `a̲` to `a̲`.

## Implementation notes

The structure map is produced by the universal property of the constant sheaf of commutative
rings, the sheafification of the constant presheaf: a map out of it is a family of ring maps
`Λ ⟶ Γ(U, f_*Λ̲)` natural in `U`. The one for `U` sends `a` to the image of `a̲` under the
sections over `U` of the direct image, which is a ring map because the ring operations of the
direct image are the direct images of the operations of `Λ̲`, read through the comparison of
products, and the operations of `Λ̲` applied to the sections `a̲`, `b̲` give `(a + b)̲`, `(ab)̲`.
No identification of `f⁻¹Λ̲` with `Λ̲` is needed for the construction.

## References

* [Stacks Project, Tag 099N](https://stacks.math.columbia.edu/tag/099N)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.RingedTopos

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]

/-- **The ringed topos `(Sh(𝒞), Λ̲)`** of a site and a commutative ring: the constant sheaf of
commutative rings on `Λ` as structure sheaf. -/
abbrev constant : RingedTopos.{u, u, u} where
  C := C
  J := J
  O := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of Λ)

/-- The ringed site presenting the constant ringed topos is the constant ringed site. -/
theorem toRingedSite_constant : (constant J Λ).toRingedSite = RingedSite.constant J Λ :=
  rfl

/-- **The global section `a̲` of `Λ̲`**, as a morphism from the terminal sheaf of sets into the
underlying sheaf of sets of the structure sheaf of rings. Its value over `U` is
`AlgebraicGeometry.RingedSite.constantSectionRingHom J Λ U a`. -/
def constantSectionHom (a : Λ) :
    ⊤_ (Sheaf J (Type u)) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) :=
  Sheaf.constHom (fun U => RingedSite.constantSectionRingHom J Λ U a)
    (fun g => ((RingedSite.constantSection J Λ a).property g))

/-- Over `U`, the morphism `constantSectionHom J Λ a` picks out the section
`RingedSite.constantSectionRingHom J Λ U a`. -/
theorem sectionsFunctor_map_constantSectionHom (a : Λ) (U : Cᵒᵖ)
    (p : (Sheaf.sectionsFunctor J U).obj (⊤_ (Sheaf J (Type u)))) :
    (Sheaf.sectionsFunctor J U).map (constantSectionHom J Λ a) p =
      RingedSite.constantSectionRingHom J Λ U a :=
  rfl

/-- The section `a̲` over `U` is the image of `a` under the sheafification map of the constant
presheaf of commutative rings. -/
theorem constantSectionRingHom_apply (U : Cᵒᵖ) (a : Λ) :
    RingedSite.constantSectionRingHom J Λ U a =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).app U).hom a := by
  let F := forget₂ CommRingCat.{u} RingCat.{u}
  let P := (Functor.const Cᵒᵖ).obj (CommRingCat.of Λ)
  let x := ((toSheafify J P).app U).hom a
  have e1 : ((sheafifyComposeIso J F P).inv.app U).hom x = ((toSheafify J (P ⋙ F)).app U).hom a :=
    ConcreteCategory.congr_hom (congr_app (sheafComposeIso_inv_fac J F P) U) a
  have e2 : ((sheafifyMap J (Functor.constComp Cᵒᵖ (CommRingCat.of Λ) F).hom).app U).hom
      (((toSheafify J (P ⋙ F)).app U).hom a) =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U).hom a :=
    (ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality J
        (Functor.constComp Cᵒᵖ (CommRingCat.of Λ) F).hom).symm U) a)
  have e3 := congr_app (constantCommuteCompose_hom_app_hom J F (CommRingCat.of Λ)) U
  have key : ((RingedSite.constantRingSheafIso' J Λ).hom.hom.app U).hom x =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U).hom a :=
    (ConcreteCategory.congr_hom e3 x).trans ((congrArg _ e1).trans e2)
  let x' : ((Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.constant J Λ).O).obj.obj U) := x
  have e4 := ConcreteCategory.congr_hom
    (congr_app (congrArg (fun φ => φ.hom) (RingedSite.constantRingSheafIso' J Λ).hom_inv_id) U) x'
  exact (congrArg (fun y => ((RingedSite.constantRingSheafIso' J Λ).inv.hom.app U).hom y)
    key.symm).trans e4

/-- The global section `(a + b)̲` is the sum of the global sections `a̲` and `b̲`. -/
theorem constantSectionHom_add (a b : Λ) :
    constantSectionHom J Λ (a + b) =
      prod.lift (constantSectionHom J Λ a) (constantSectionHom J Λ b) ≫
        Sheaf.ringAddHom (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  rw [Functor.map_comp, types_comp_apply, Functor.map_lift_apply,
    Sheaf.sectionsFunctor_map_ringAddHom]
  exact map_add (RingedSite.constantSectionRingHom J Λ U) a b

/-- The global section `(ab)̲` is the product of the global sections `a̲` and `b̲`. -/
theorem constantSectionHom_mul (a b : Λ) :
    constantSectionHom J Λ (a * b) =
      prod.lift (constantSectionHom J Λ a) (constantSectionHom J Λ b) ≫
        Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  rw [Functor.map_comp, types_comp_apply, Functor.map_lift_apply,
    Sheaf.sectionsFunctor_map_ringMulHom]
  exact map_mul (RingedSite.constantSectionRingHom J Λ U) a b

/-- The global section `0̲` is the zero section of `Λ̲`. -/
theorem constantSectionHom_zero :
    constantSectionHom J Λ 0 =
      Sheaf.ringZeroHom (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  rw [Sheaf.sectionsFunctor_map_ringZeroHom]
  exact map_zero (RingedSite.constantSectionRingHom J Λ U)

/-- The global section `1̲` is the unit section of `Λ̲`. -/
theorem constantSectionHom_one :
    constantSectionHom J Λ 1 =
      Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  rw [Sheaf.sectionsFunctor_map_ringOneHom]
  exact map_one (RingedSite.constantSectionRingHom J Λ U)

end AlgebraicGeometry.RingedTopos

namespace MorphismOfTopoi

open AlgebraicGeometry

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{u} D] {K : GrothendieckTopology D} (Λ : Type u) [CommRing Λ]
  (f : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf J (Type u)))

/-- The section of the direct image of `Λ̲` over `U` which is the direct image of `a̲`. -/
def constantPushforwardSection (U : Cᵒᵖ) (a : Λ) :
    (f.pushforward ⋙ Sheaf.sectionsFunctor J U).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)) :=
  (f.pushforward ⋙ Sheaf.sectionsFunctor J U).map (RingedTopos.constantSectionHom K Λ a) default

/-- The ring map `Λ ⟶ Γ(U, f_*Λ̲)`, `a ↦ f_*(a̲)`. -/
def constantPushforwardRingHom (U : Cᵒᵖ) :
    CommRingCat.of Λ ⟶
      ((pushforwardCommRingFunctor f).obj (RingedTopos.constant K Λ).O).obj.obj U :=
  letI := Stacks.Sheaves.RingedToposModules.inverseImageSectionsCommRing J f.pushforward
    (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)
    (commRingSheaf_mul_comm (RingedTopos.constant K Λ).O) U
  CommRingCat.ofHom
    { toFun := constantPushforwardSection Λ f U
      map_one' := by
        change _ = Sheaf.ringOneObj _ _
        rw [constantPushforwardSection, RingedTopos.constantSectionHom_one]
        exact congrArg _ (Subsingleton.elim _ _)
      map_mul' := fun a b => by
        change _ = Sheaf.ringMulObj _ _ _ _
        rw [constantPushforwardSection, RingedTopos.constantSectionHom_mul, Functor.map_comp,
          types_comp_apply, Functor.map_lift_apply]
        rfl
      map_zero' := by
        change _ = Sheaf.ringZeroObj _ _
        rw [constantPushforwardSection, RingedTopos.constantSectionHom_zero]
        exact congrArg _ (Subsingleton.elim _ _)
      map_add' := fun a b => by
        change _ = Sheaf.ringAddObj _ _ _ _
        rw [constantPushforwardSection, RingedTopos.constantSectionHom_add, Functor.map_comp,
          types_comp_apply, Functor.map_lift_apply]
        rfl }

/-- The ring map `Λ ⟶ Γ(U, f_*Λ̲)` sends `a` to the direct image of `a̲`. -/
theorem constantPushforwardRingHom_apply (U : Cᵒᵖ) (a : Λ) :
    (constantPushforwardRingHom Λ f U).hom a = constantPushforwardSection Λ f U a :=
  rfl

/-- The ring maps `Λ ⟶ Γ(U, f_*Λ̲)` as a morphism of presheaves of commutative rings out of the
constant presheaf. -/
def constantPushforwardNatTrans :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of Λ) ⟶
      ((pushforwardCommRingFunctor f).obj (RingedTopos.constant K Λ).O).obj where
  app U := constantPushforwardRingHom Λ f U
  naturality {U U'} g := by
    ext a
    change constantPushforwardSection Λ f U' a =
      ((f.pushforward.obj (Sheaf.ringSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O))).obj.map g)
        (constantPushforwardSection Λ f U a)
    rw [constantPushforwardSection, constantPushforwardSection, Functor.comp_map,
      Functor.comp_map]
    have hd : (default : (f.pushforward ⋙ Sheaf.sectionsFunctor J U').obj
        (⊤_ (Sheaf K (Type u)))) =
        (f.pushforward.obj (⊤_ (Sheaf K (Type u)))).obj.map g
          (default : (f.pushforward ⋙ Sheaf.sectionsFunctor J U).obj (⊤_ (Sheaf K (Type u)))) :=
      Subsingleton.elim _ _
    rw [hd]
    exact NatTrans.naturality_apply
      (f.pushforward.map (RingedTopos.constantSectionHom K Λ a)).hom g _

/-- **The morphism of ringed topoi `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)` underlain by a morphism of topoi
`f : Sh(𝒟) ⟶ Sh(𝒞)`.** Its structure map `Λ̲ ⟶ f_*Λ̲` is the map of sheaves of commutative
rings out of the constant sheaf determined by `a̲ ↦ f_*(a̲)`. -/
def constantRingedToposHom :
    RingedToposHom (RingedTopos.constant K Λ) (RingedTopos.constant J Λ) where
  toToposHom := f
  fSharp := ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm
    (constantPushforwardNatTrans Λ f)

/-- **The structure map of `MorphismOfTopoi.constantRingedToposHom` on a global section `a̲`**:
over every `U`, it carries `a̲` to the direct image of `a̲`. -/
theorem fSharp_app_constantSectionRingHom (U : Cᵒᵖ) (a : Λ) :
    ((constantRingedToposHom Λ f).fSharp.hom.app U).hom
        (RingedSite.constantSectionRingHom J Λ U a) =
      constantPushforwardSection Λ f U a := by
  rw [RingedTopos.constantSectionRingHom_apply]
  have h := ((sheafificationAdjunction J CommRingCat.{u}).homEquiv
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))
    ((pushforwardCommRingFunctor f).obj (RingedTopos.constant K Λ).O)).apply_symm_apply
    (constantPushforwardNatTrans Λ f)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.app U) h) a

/-- **In inverse-image form, the structure map carries the inverse image of `a̲` to `a̲`.** The
composite of the inverse image of the global section `a̲` of `Λ̲` on `𝒞` with the underlying
map of the structure map `f⁻¹Λ̲ ⟶ Λ̲` is the global section `a̲` on `𝒟`, read through the
comparison `f⁻¹1 ≅ 1`. -/
theorem map_constantSectionHom_comp_fSharpInverseImageRing (a : Λ) :
    f.inverseImage.map (RingedTopos.constantSectionHom J Λ a) ≫
        (sheafCompose K (forget RingCat.{u})).map
          (constantRingedToposHom Λ f).fSharpInverseImageRing =
      f.inverseImageTerminalIso.hom ≫ RingedTopos.constantSectionHom K Λ a := by
  apply (f.adj.homEquiv _ _).injective
  refine (f.adj.homEquiv_naturality_left _ _).trans ?_
  refine (congrArg (fun m => RingedTopos.constantSectionHom J Λ a ≫ m)
    (RingedToposHom.fSharpInverseImageRing_adjunct (constantRingedToposHom Λ f)).symm).trans ?_
  refine Sheaf.hom_ext_sections fun U s => ?_
  refine (fSharp_app_constantSectionRingHom Λ f U a).trans ?_
  rw [Adjunction.homEquiv_unit, f.pushforward.map_comp]
  exact congrArg ((f.pushforward ⋙ Sheaf.sectionsFunctor J U).map
    (RingedTopos.constantSectionHom K Λ a))
    (Subsingleton.elim (α := (f.pushforward ⋙ Sheaf.sectionsFunctor J U).obj
      (⊤_ (Sheaf K (Type u)))) default ((Sheaf.sectionsFunctor J U).map
        (f.adj.unit.app _ ≫ f.pushforward.map f.inverseImageTerminalIso.hom) s))

end MorphismOfTopoi

end
