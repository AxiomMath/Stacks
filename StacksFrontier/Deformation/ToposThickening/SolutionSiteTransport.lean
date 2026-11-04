module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentBaseIso
public import StacksFrontier.Deformation.AlgebraExtension.SiteEquivalence
public import StacksFrontier.Deformation.ToposThickening.SolutionClassesAlgebraExtensionEquiv

/-!
# Transporting a square-zero extension problem to an equivalent site

Let `X = (Sh(𝒞), 𝒪)` be a ringed topos, `e : 𝒞 ≌ 𝒟` an equivalence of categories and `K` a
topology on `𝒟` for which `G = e.inverse : 𝒟 ⥤ 𝒞` is a dense subsite, so that restriction along `G`
is an equivalence `Sh(𝒞) ≌ Sh(𝒟)`. Write `X' = (Sh(𝒟), G^s𝒪)`.

A square-zero extension problem `S` of [Stacks Project, Tag 08UF] on `X`, over a base `ℬ`, is
transported to a problem `S'` on `X'` over the same base: the morphism `f' : X' ⟶ ℬ` is the
composite of the equivalence `Sh(𝒟) ≅ Sh(𝒞)` with `f`, the ideal and the prescribed module are the
restrictions along `G`, and the inclusion of the ideal and the prescribed map `c` are restricted
section by section. Reading solutions as extensions of algebras, restriction along `G` is an
equivalence of categories of extensions
(`Deformation.AlgebraExtension.isEquivalence_siteRestriction`)
which preserves and reflects compatibility with `c`, so the isomorphism classes of solutions of
`S` and of `S'` correspond.

This is how the problem on the small étale site of an algebraic space, whose objects lie in
`Type (u + 1)`, is moved to the model of that site in `Type u`, in the proof of
[Stacks Project, Tag 0D17].

## Main definitions

* `AlgebraicGeometry.RingedTopos.ofSiteEquivalence`: the ringed topos `X'`.
* `AlgebraicGeometry.RingedTopos.ofSiteEquivalenceToposHom`: the equivalence `Sh(𝒟) ⟶ Sh(𝒞)` as a
  morphism of topoi, with inverse image restriction along `G`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.siteTransport`: the problem `S'`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.siteTransportIsomorphismClassesEquiv`:
  the bijection of isomorphism classes of solutions.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.ToposPullback

universe u v₁ w₁ v₂ w₂ v' u' z t

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{w₁, v₁, u}) {D : Type v₂} [Category.{w₂} D]
  (K : GrothendieckTopology D) (e : X.C ≌ D) [e.inverse.IsDenseSubsite K X.J]

/-- **The ringed topos `(Sh(𝒟), G^s𝒪)`** on a site `𝒟` equivalent to the site of `X`, with the
restriction of the structure sheaf along `G = e.inverse`. -/
abbrev ofSiteEquivalence : RingedTopos.{w₂, v₂, u} where
  C := D
  J := K
  O := (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).obj X.O

/-- **The equivalence `Sh(𝒟) ⟶ Sh(𝒞)` as a morphism of topoi**: its inverse image is restriction
along `G = e.inverse`, its direct image restriction along `e.functor`. -/
def ofSiteEquivalenceToposHom : MorphismOfTopoi (X.ofSiteEquivalence K e).Topos X.Topos where
  pushforward := e.functor.sheafPushforwardContinuous (Type u) X.J K
  inverseImage := e.inverse.sheafPushforwardContinuous (Type u) K X.J
  adj := (Equivalence.sheafCongr X.J K e (Type u)).toAdjunction
  preservesFiniteLimits := inferInstance

end AlgebraicGeometry.RingedTopos

namespace Deformation.AlgebraExtension

/-! ### Restricting the ideal data of a problem along a functor of sites

The constructions below are stated for abstract sheaves of rings, so that no inverse image of a
sheaf of rings is unfolded when they are applied. -/

section IdealRestriction

/-- Equal morphisms of sheaves of rings agree on sections. -/
private theorem hom_app_apply_congr {E : Type v₁} [Category.{w₁} E] {L : GrothendieckTopology E}
    {R R' : Sheaf L CommRingCat.{u}} {f g : R ⟶ R'} (h : f = g) (V : Eᵒᵖ) (r : R.obj.obj V) :
    f.hom.app V r = g.hom.app V r :=
  congrArg (fun k => k.hom.app V r) h

/-- An isomorphism of sheaves of rings is inverted on sections by its inverse. -/
private theorem iso_inv_hom_app_hom_app_apply {E : Type v₁} [Category.{w₁} E]
    {L : GrothendieckTopology E} {R R' : Sheaf L CommRingCat.{u}} (φ : R ≅ R') (V : Eᵒᵖ)
    (y : R.obj.obj V) : φ.inv.hom.app V (φ.hom.hom.app V y) = y :=
  hom_app_apply_congr φ.hom_inv_id V y

/-- An isomorphism of sheaves of rings is inverted on sections by its inverse. -/
private theorem iso_hom_inv_app_hom_app_apply {E : Type v₁} [Category.{w₁} E]
    {L : GrothendieckTopology E} {R R' : Sheaf L CommRingCat.{u}} (φ : R ≅ R') (V : Eᵒᵖ)
    (y : R'.obj.obj V) : φ.hom.hom.app V (φ.inv.hom.app V y) = y :=
  hom_app_apply_congr φ.inv_hom_id V y

variable {C : Type v₁} [Category.{w₁} C] {J : GrothendieckTopology C}
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (G : D ⥤ C)
  [G.IsContinuous K J] [G.IsCocontinuous K J]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {T₁ T₂ : Sheaf J CommRingCat.{u}} {R₁ R₂ : Sheaf K CommRingCat.{u}}
  {σ : T₂ ⟶ T₁} {ρ : R₂ ⟶ R₁} (φ₁ : R₁ ≅ (ringRes K G).obj T₁) (φ₂ : R₂ ≅ (ringRes K G).obj T₂)
  (I : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₁))

/-- The restriction `G^sℐ` of a `T₁`-module, read as an `R₁`-module through `φ₁ : R₁ ≅ G^sT₁`. -/
abbrev restrictModuleVia :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁) :=
  (SheafOfModules.restrictScalars ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
    φ₁.hom)).obj ((moduleRes K G T₁).obj I)

variable {K G φ₁ I}

/-- **The restriction of an ideal inclusion** `ℐ ⟶ T₂` (linear over `σ : T₂ ⟶ T₁`) to an inclusion
`G^sℐ ⟶ G^sT₂ ≅ R₂`, linear over `ρ : R₂ ⟶ R₁`, for `φ₁ ∘ ρ = G^sσ ∘ φ₂`. -/
def restrictIdealInclusion (hφ : ρ ≫ φ₁.hom = φ₂.hom ≫ (ringRes K G).map σ)
    (ι : (SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map σ)).obj I ⟶
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₂)) :
    (SheafOfModules.restrictScalars ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
        ρ)).obj (restrictModuleVia K G φ₁ I) ⟶
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R₂) where
  val :=
    { app := fun V => ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map ρ)).obj
            (restrictModuleVia K G φ₁ I)).val.obj V)
        (Y := (SheafOfModules.unit
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R₂)).val.obj V)
        { toFun := fun x => φ₂.inv.hom.app V (ι.val.app (G.op.obj V) x)
          map_add' := fun x y =>
            (congrArg _ (map_add (ConcreteCategory.hom (ι.val.app (G.op.obj V))) x y)).trans
              (map_add _ _ _)
          map_smul' := fun r x => by
            have hn : φ₁.hom.hom.app V (ρ.hom.app V r) =
                σ.hom.app (G.op.obj V) (φ₂.hom.hom.app V r) :=
              congrArg (fun k => k.hom.app V r) hφ
            have hr : φ₂.inv.hom.app V (φ₂.hom.hom.app V r) = r :=
              congrArg (fun k => k.hom.app V r) φ₂.hom_inv_id
            change φ₂.inv.hom.app V (ι.val.app (G.op.obj V)
                (show I.val.obj (G.op.obj V) from
                  (show ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₁).obj.obj
                    (G.op.obj V) from φ₁.hom.hom.app V (ρ.hom.app V r)) •
                  (show I.val.obj (G.op.obj V) from x))) =
              (show R₂.obj.obj V from r) * φ₂.inv.hom.app V (ι.val.app (G.op.obj V) x)
            rw [hn]
            refine (congrArg (φ₂.inv.hom.app V) ((ConcreteCategory.hom
              (ι.val.app (G.op.obj V))).map_smul (φ₂.hom.hom.app V r) x)).trans ?_
            exact ((φ₂.inv.hom.app V).hom.map_mul _ _).trans
              (congrArg (· * φ₂.inv.hom.app V (ι.val.app (G.op.obj V) x)) hr) }
      naturality := fun {V W} g => by
        ext x
        exact (congrArg (φ₂.inv.hom.app W)
          (PresheafOfModules.naturality_apply ι.val (G.op.map g) x)).trans
            (NatTrans.naturality_apply φ₂.inv.hom g _) }

omit [G.IsCocontinuous K J] in
/-- On sections over `V`, the restricted inclusion is `ι` over `G(V)` followed by `φ₂⁻¹`. -/
theorem restrictIdealInclusion_val_app (hφ : ρ ≫ φ₁.hom = φ₂.hom ≫ (ringRes K G).map σ)
    (ι : (SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map σ)).obj I ⟶
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₂))
    (V : Dᵒᵖ) (x : I.val.obj (G.op.obj V)) :
    (restrictIdealInclusion φ₂ hφ ι).val.app V x = φ₂.inv.hom.app V (ι.val.app (G.op.obj V) x) :=
  rfl

omit [G.IsCocontinuous K J] in
/-- The restricted inclusion is killed by `ρ` when the inclusion is killed by `σ`. -/
theorem restrictIdealInclusion_zero (hφ : ρ ≫ φ₁.hom = φ₂.hom ≫ (ringRes K G).map σ)
    (ι : (SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map σ)).obj I ⟶
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₂))
    (hzero : ∀ (U : Cᵒᵖ) (m : I.val.obj U),
      σ.hom.app U (show T₂.obj.obj U from ι.val.app U m) = 0)
    (V : Dᵒᵖ) (m : I.val.obj (G.op.obj V)) :
    ρ.hom.app V (show R₂.obj.obj V from (restrictIdealInclusion φ₂ hφ ι).val.app V m) = 0 := by
  have h1 : φ₁.hom.hom.app V (ρ.hom.app V (φ₂.inv.hom.app V (ι.val.app (G.op.obj V) m))) =
      σ.hom.app (G.op.obj V) (φ₂.hom.hom.app V (φ₂.inv.hom.app V (ι.val.app (G.op.obj V) m))) :=
    hom_app_apply_congr hφ V _
  exact (iso_inv_hom_app_hom_app_apply φ₁ V _).symm.trans ((congrArg (φ₁.inv.hom.app V) h1).trans
    ((congrArg (fun z => φ₁.inv.hom.app V (σ.hom.app (G.op.obj V) z))
      (iso_hom_inv_app_hom_app_apply φ₂ V _)).trans
        ((congrArg (φ₁.inv.hom.app V) (hzero _ m)).trans (map_zero _))))

omit [G.IsCocontinuous K J] in
/-- The restricted inclusion identifies the restricted module with the kernel of `ρ`, when the
inclusion identifies `ℐ` with the kernel of `σ`. -/
theorem restrictIdealInclusion_universal (hφ : ρ ≫ φ₁.hom = φ₂.hom ≫ (ringRes K G).map σ)
    (ι : (SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map σ)).obj I ⟶
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₂))
    (huniv : ∀ (U : Cᵒᵖ) (a : T₂.obj.obj U), σ.hom.app U a = 0 →
      ∃! m : I.val.obj U, (show T₂.obj.obj U from ι.val.app U m) = a)
    (V : Dᵒᵖ) (a : R₂.obj.obj V) (ha : ρ.hom.app V a = 0) :
    ∃! m : I.val.obj (G.op.obj V),
      (show R₂.obj.obj V from (restrictIdealInclusion φ₂ hφ ι).val.app V m) = a := by
  have h1 : φ₁.hom.hom.app V (ρ.hom.app V a) = σ.hom.app (G.op.obj V) (φ₂.hom.hom.app V a) :=
    hom_app_apply_congr hφ V a
  rw [ha, map_zero] at h1
  obtain ⟨m, hm, hu⟩ := huniv (G.op.obj V) (φ₂.hom.hom.app V a) h1.symm
  refine ⟨m, ?_, fun m' hm' => hu m' ?_⟩
  · exact (congrArg (φ₂.inv.hom.app V) hm).trans (iso_inv_hom_app_hom_app_apply φ₂ V a)
  · exact (iso_hom_inv_app_hom_app_apply φ₂ V _).symm.trans (congrArg (φ₂.hom.hom.app V) hm')

variable {O : Sheaf J CommRingCat.{u}} {ψ : T₁ ⟶ O} {ψ' : R₁ ⟶ (ringRes K G).obj O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **The restriction of a prescribed map** `ℐ ⟶ ℳ` (linear over `ψ : T₁ ⟶ 𝒪`) to a map
`G^sℐ ⟶ G^sℳ`, linear over `ψ' = G^sψ ∘ φ₁ : R₁ ⟶ G^s𝒪`. -/
def restrictPrescribedMap (hψ : ψ' = φ₁.hom ≫ (ringRes K G).map ψ)
    (c : I ⟶ (SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map ψ)).obj M) :
    restrictModuleVia K G φ₁ I ⟶ (SheafOfModules.restrictScalars ((sheafCompose K
      (forget₂ CommRingCat.{u} RingCat.{u})).map ψ')).obj ((moduleRes K G O).obj M) where
  val :=
    { app := fun V => ModuleCat.ofHom
        (X := (restrictModuleVia K G φ₁ I).val.obj V)
        (Y := ((SheafOfModules.restrictScalars ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).map ψ')).obj
            ((moduleRes K G O).obj M)).val.obj V)
        { toFun := fun x => c.val.app (G.op.obj V) x
          map_add' := fun x y => map_add (ConcreteCategory.hom (c.val.app (G.op.obj V))) x y
          map_smul' := fun r x => by
            have hn : ψ'.hom.app V r = ψ.hom.app (G.op.obj V) (φ₁.hom.hom.app V r) :=
              congrArg (fun k => k.hom.app V r) hψ
            change c.val.app (G.op.obj V)
                (show I.val.obj (G.op.obj V) from
                  (show ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T₁).obj.obj
                    (G.op.obj V) from φ₁.hom.hom.app V r) •
                  (show I.val.obj (G.op.obj V) from x)) =
              (show M.val.obj (G.op.obj V) from
                (show ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).obj.obj
                  (G.op.obj V) from ψ'.hom.app V r) •
                (show M.val.obj (G.op.obj V) from c.val.app (G.op.obj V) x))
            rw [hn]
            exact (ConcreteCategory.hom (c.val.app (G.op.obj V))).map_smul
              (φ₁.hom.hom.app V r) x }
      naturality := fun {V W} g => by
        ext x
        exact PresheafOfModules.naturality_apply c.val (G.op.map g) x }

omit [G.IsCocontinuous K J] in
/-- On sections over `V`, the restricted prescribed map is `c` over `G(V)`. -/
theorem restrictPrescribedMap_val_app (hψ : ψ' = φ₁.hom ≫ (ringRes K G).map ψ)
    (c : I ⟶ (SheafOfModules.restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map ψ)).obj M)
    (V : Dᵒᵖ) (x : I.val.obj (G.op.obj V)) :
    (restrictPrescribedMap hψ c).val.app V x = c.val.app (G.op.obj V) x :=
  rfl

omit [G.IsCocontinuous K J] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The two compatibilities of `restrictIdealInclusion` and `restrictPrescribedMap` combine:
`ψ' ∘ ρ ∘ φ₂⁻¹ = G^s(ψ ∘ σ)`. -/
theorem restrict_comm_aux {O : Sheaf J CommRingCat.{u}} {ψ : T₁ ⟶ O}
    {ψ' : R₁ ⟶ (ringRes K G).obj O} (φ₁ : R₁ ≅ (ringRes K G).obj T₁)
    (φ₂ : R₂ ≅ (ringRes K G).obj T₂) (hφ : ρ ≫ φ₁.hom = φ₂.hom ≫ (ringRes K G).map σ)
    (hψ : ψ' = φ₁.hom ≫ (ringRes K G).map ψ) :
    φ₂.inv ≫ ρ ≫ ψ' = (ringRes K G).map (σ ≫ ψ) := by
  rw [hψ, ← Category.assoc ρ, hφ, Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]

end IdealRestriction

end Deformation.AlgebraExtension

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry

variable {X : RingedTopos.{w₁, v₁, u}} {B : RingedTopos.{v', u', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {D : Type v₂} [Category.{w₂} D] (K : GrothendieckTopology D) (e : X.C ≌ D)
  [e.inverse.IsDenseSubsite K X.J]
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/-- **The inverse image along the transported morphism is restriction of the inverse image**:
for `f' = f ∘ (Sh(𝒟) ≅ Sh(𝒞))`, `f'⁻¹R ≅ G^s(f⁻¹R)`, naturally in the sheaf of rings `R`. -/
def siteTransportInverseImageIso (f : MorphismOfTopoi X.Topos B.Topos) :
    inverseImageCommRingFunctor (f.comp (X.ofSiteEquivalenceToposHom K e)) ≅
      inverseImageCommRingFunctor f ⋙ e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J :=
  (pullbackCommRingSheafFunctorComp X.J K f.inverseImage
      (e.inverse.sheafPushforwardContinuous (Type u) K X.J)).symm ≪≫
    Functor.isoWhiskerLeft (inverseImageCommRingFunctor f)
      (NatIso.ofComponents (fun R => restrictionCommRingIso K X.J e.inverse R)
        (fun a => restrictionCommRingIso_naturality K X.J e.inverse a))

/-- **The transported morphism of ringed topoi `f' : X' ⟶ ℬ`**: the composite of the equivalence
`Sh(𝒟) ≅ Sh(𝒞)` with `f`, with structure map `f'⁻¹𝒪_ℬ ≅ G^s(f⁻¹𝒪_ℬ) ⟶ G^s𝒪` the restriction of
that of `f`. -/
def siteTransportHom (f : RingedToposHom X B) : RingedToposHom (X.ofSiteEquivalence K e) B :=
  RingedToposHom.ofInverseImageMap (f.toToposHom.comp (X.ofSiteEquivalenceToposHom K e))
    ((siteTransportInverseImageIso K e f.toToposHom).hom.app B.O ≫
      (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map f.fSharpInverseImage)

/-- The structure map of `f'` is `f'⁻¹𝒪_ℬ ≅ G^s(f⁻¹𝒪_ℬ)` followed by the restriction of the
structure map of `f`. -/
theorem siteTransportHom_fSharpInverseImage (f : RingedToposHom X B) :
    (siteTransportHom K e f).fSharpInverseImage =
      (siteTransportInverseImageIso K e f.toToposHom).hom.app B.O ≫
        (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map f.fSharpInverseImage :=
  RingedToposHom.ofInverseImageMap_fSharpInverseImage _ _

/-- The restriction of the structure map of `f` is that of `f'`, read through
`f'⁻¹𝒪_ℬ ≅ G^s(f⁻¹𝒪_ℬ)`. -/
theorem sheafPushforwardContinuous_map_fSharpInverseImage (f : RingedToposHom X B) :
    (e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map f.fSharpInverseImage =
      ((siteTransportInverseImageIso K e f.toToposHom).app B.O).symm.hom ≫
        (siteTransportHom K e f).fSharpInverseImage := by
  rw [siteTransportHom_fSharpInverseImage, Iso.symm_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]


variable (S : RingedToposExtensionProblem X B)

/-- The naturality of `f'⁻¹R ≅ G^s(f⁻¹R)`, on sections. -/
theorem siteTransportInverseImageIso_hom_naturality_apply {R R' : Sheaf B.J CommRingCat.{u}}
    (a : R ⟶ R') (V : Dᵒᵖ)
    (r : ((inverseImageCommRingFunctor (S.f.toToposHom.comp
      (X.ofSiteEquivalenceToposHom K e))).obj R).obj.obj V) :
    ((siteTransportInverseImageIso K e S.f.toToposHom).hom.app R').hom.app V
        (((inverseImageCommRingFunctor (S.f.toToposHom.comp
          (X.ofSiteEquivalenceToposHom K e))).map a).hom.app V r) =
      ((inverseImageCommRingFunctor S.f.toToposHom).map a).hom.app (e.inverse.op.obj V)
        (((siteTransportInverseImageIso K e S.f.toToposHom).hom.app R).hom.app V r) :=
  congrArg (fun k => k.hom.app V r)
    ((siteTransportInverseImageIso K e S.f.toToposHom).hom.naturality a)

/-- **The transported ideal** `G^s(f⁻¹𝒥)`, a module over `f'⁻¹𝒪_ℬ` through
`f'⁻¹𝒪_ℬ ≅ G^s(f⁻¹𝒪_ℬ)`. -/
abbrev siteTransportIdeal :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
      ((inverseImageCommRingFunctor (siteTransportHom K e S.f).toToposHom).obj B.O)) :=
  (SheafOfModules.restrictScalars ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((siteTransportInverseImageIso K e S.f.toToposHom).hom.app B.O))).obj
    ((Deformation.AlgebraExtension.moduleRes K e.inverse
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj S.I)


/-- `f'⁻¹𝒪_{ℬ'} ≅ G^s(f⁻¹𝒪_{ℬ'})` and `f'⁻¹𝒪_ℬ ≅ G^s(f⁻¹𝒪_ℬ)` are compatible with the inverse
images of the base reduction. -/
theorem siteTransport_comm :
    (inverseImageCommRingFunctor (siteTransportHom K e S.f).toToposHom).map S.baseReduction ≫
        ((siteTransportInverseImageIso K e S.f.toToposHom).app B.O).hom =
      ((siteTransportInverseImageIso K e S.f.toToposHom).app S.baseExtension).hom ≫
        (Deformation.AlgebraExtension.ringRes K e.inverse).map
          ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) :=
  (siteTransportInverseImageIso K e S.f.toToposHom).hom.naturality S.baseReduction

/-- **The square-zero extension problem transported to the equivalent site**: over the same
thickened base, with `f' = f ∘ (Sh(𝒟) ≅ Sh(𝒞))`, ideal `G^s(f⁻¹𝒥)`, prescribed module `G^s𝒢`, and
the inclusion of the ideal and the prescribed map restricted section by section. -/
abbrev siteTransport : RingedToposExtensionProblem (X.ofSiteEquivalence K e) B where
  f := siteTransportHom K e S.f
  baseExtension := S.baseExtension
  baseReduction := S.baseReduction
  baseLocallySurjective := S.baseLocallySurjective
  baseSquareZero := S.baseSquareZero
  I := Deformation.AlgebraExtension.restrictModuleVia K e.inverse
    ((siteTransportInverseImageIso K e S.f.toToposHom).app B.O) S.I
  G := (Deformation.AlgebraExtension.moduleRes K e.inverse X.O).obj S.G
  idealInclusion := Deformation.AlgebraExtension.restrictIdealInclusion
    ((siteTransportInverseImageIso K e S.f.toToposHom).app S.baseExtension)
    (siteTransport_comm K e S) S.idealInclusion
  c := Deformation.AlgebraExtension.restrictPrescribedMap
    (siteTransportHom_fSharpInverseImage K e S.f) S.c
  idealZero := Deformation.AlgebraExtension.restrictIdealInclusion_zero _
    (siteTransport_comm K e S) S.idealInclusion S.idealZero
  idealUniversal := Deformation.AlgebraExtension.restrictIdealInclusion_universal _
    (siteTransport_comm K e S) S.idealInclusion S.idealUniversal

/-- The ring map `f⁻¹𝒪_{ℬ'} ⟶ f⁻¹𝒪_ℬ ⟶ 𝒪` over which the solutions of `S` are algebra
extensions. -/
abbrev siteTransportBaseMap :
    (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ X.O :=
  (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫ S.f.fSharpInverseImage

/-- The identification `G^s(f⁻¹𝒪_{ℬ'}) ≅ f'⁻¹𝒪_{ℬ'}` through which the solutions of the transported
problem are algebra extensions over the restriction of `f⁻¹𝒪_{ℬ'}`. -/
abbrev siteTransportBaseIso :
    (Deformation.AlgebraExtension.ringRes K e.inverse).obj
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) ≅
      (inverseImageCommRingFunctor (S.siteTransport K e).f.toToposHom).obj
        (S.siteTransport K e).baseExtension :=
  ((siteTransportInverseImageIso K e S.f.toToposHom).app S.baseExtension).symm

/-- Under `G^s(f⁻¹𝒪_{ℬ'}) ≅ f'⁻¹𝒪_{ℬ'}`, the ring map `f'⁻¹𝒪_{ℬ'} ⟶ f'⁻¹𝒪_ℬ ⟶ 𝒪` of the
transported problem is the restriction of `siteTransportBaseMap`. -/
theorem siteTransportBaseIso_comm :
    (S.siteTransportBaseIso K e).hom ≫
        (inverseImageCommRingFunctor (S.siteTransport K e).f.toToposHom).map
          (S.siteTransport K e).baseReduction ≫ (S.siteTransport K e).f.fSharpInverseImage =
      (Deformation.AlgebraExtension.ringRes K e.inverse).map (S.siteTransportBaseMap) :=
  Deformation.AlgebraExtension.restrict_comm_aux _ _ (siteTransport_comm K e S)
    (siteTransportHom_fSharpInverseImage K e S.f)

/-- **Restriction to the equivalent site preserves and reflects compatibility with `c`.** -/
theorem siteTransport_isCompatible_iff
    (Q : Deformation.AlgebraExtension S.siteTransportBaseMap S.G) :
    S.IsCompatible (Iso.refl _) S.c Q ↔
      (S.siteTransport K e).IsCompatible (S.siteTransportBaseIso K e) (S.siteTransport K e).c
        ((Deformation.AlgebraExtension.siteRestriction K e S.siteTransportBaseMap S.G).obj Q) := by
  have key : ∀ (V : Dᵒᵖ) (x : S.I.val.obj (e.inverse.op.obj V)),
      (S.siteTransport K e).idealImage (U := V) (S.siteTransportBaseIso K e)
          ((Deformation.AlgebraExtension.siteRestriction K e S.siteTransportBaseMap S.G).obj Q) x =
        S.idealImage (Iso.refl _) Q x := fun V x =>
    congrArg (Q.algebraMap.hom.app (e.inverse.op.obj V))
      (congrArg (fun k => k.hom.app V (S.idealInclusion.val.app (e.inverse.op.obj V) x))
        ((siteTransportInverseImageIso K e S.f.toToposHom).app S.baseExtension).inv_hom_id)
  constructor
  · intro h V x
    exact (key V x).trans (h _ x)
  · intro h
    exact S.isCompatible_of_essSurj (Iso.refl _) e.inverse Q fun V x => (key V x).symm.trans (h V x)

variable [X.J.HasSheafCompose (forget CommRingCat.{u})] [K.HasSheafCompose (forget CommRingCat.{u})]

/-- **The isomorphism classes of solutions of `S` and of its transport correspond**: a solution is
read as an extension of `f⁻¹𝒪_{ℬ'}`-algebras and restricted along `G`. -/
def siteTransportIsomorphismClassesEquiv :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      CompatibleFirstOrderThickening.IsomorphismClasses (S.siteTransport K e) :=
  have := Deformation.AlgebraExtension.isEquivalence_siteRestriction K e S.siteTransportBaseMap S.G
  isomorphismClassesEquivOfAlgebraExtension S (S.siteTransport K e) (Iso.refl _)
    (Category.id_comp _) (S.siteTransportBaseIso K e) (siteTransportBaseIso_comm K e S)
    (Deformation.AlgebraExtension.siteRestriction K e S.siteTransportBaseMap S.G)
    (siteTransport_isCompatible_iff K e S)

/-- **The solution of the transported problem attached to a solution of `S`**: its middle term is
the restriction of that of the solution along `G`. -/
abbrev siteTransportSolution (P : S.CompatibleFirstOrderThickening) :
    (S.siteTransport K e).CompatibleFirstOrderThickening :=
  transportSolution S (S.siteTransport K e) (Iso.refl _) (Category.id_comp _)
    (S.siteTransportBaseIso K e) (siteTransportBaseIso_comm K e S)
    (Deformation.AlgebraExtension.siteRestriction K e S.siteTransportBaseMap S.G)
    (siteTransport_isCompatible_iff K e S) P

/-- `siteTransportIsomorphismClassesEquiv` sends the class of a solution `P` to the class of
`siteTransportSolution P`. -/
theorem siteTransportIsomorphismClassesEquiv_mk (P : S.CompatibleFirstOrderThickening) :
    siteTransportIsomorphismClassesEquiv K e S
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S) P) =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid (S.siteTransport K e))
        (S.siteTransportSolution K e P) :=
  rfl

section Ext

variable (f : RingedToposHom X B) [HasWeakSheafify K CommRingCat.{u}]
  [HasSheafify K AddCommGrpCat.{max u v₂ w₂ z}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v₂ w₂ z}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{max u v₂ w₂ z}
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.ofSiteEquivalence K e).O))]
  (M : _root_.SheafOfModules.{max u v₂ w₂ z}
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.ofSiteEquivalence K e).O))

/-- **`Ext` out of the naive cotangent complex of the transported structure map**: it is `Ext` out
of `NL` of the restriction `G^s(f⁻¹𝒪_ℬ) ⟶ G^s𝒪` of the structure map of `f`, through
`f'⁻¹𝒪_ℬ ≅ G^s(f⁻¹𝒪_ℬ)`. -/
def siteTransportNaiveCotangentExtAddEquiv (n : ℤ) :
    Stacks.SheafOfModules.naiveCotangentExt.{w₂, v₂, u, z, t} K
        ((e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).obj
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O))
        (X.ofSiteEquivalence K e).O
        ((e.inverse.sheafPushforwardContinuous CommRingCat.{u} K X.J).map f.fSharpInverseImage)
        M n ≃+
      Stacks.SheafOfModules.naiveCotangentExt.{w₂, v₂, u, z, t} (X.ofSiteEquivalence K e).J
        ((inverseImageCommRingFunctor (siteTransportHom K e f).toToposHom).obj B.O)
        (X.ofSiteEquivalence K e).O (siteTransportHom K e f).fSharpInverseImage M n :=
  Stacks.SheafOfModules.naiveCotangentExtAddEquivOfBaseIso.{w₂, v₂, u, z, t} K
    ((siteTransportInverseImageIso K e f.toToposHom).app B.O).symm _ _
    (sheafPushforwardContinuous_map_fSharpInverseImage K e f) M n

end Ext

end Deformation.ToposThickening.RingedToposExtensionProblem

end
