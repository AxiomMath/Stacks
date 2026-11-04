module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PiEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Basic
public import StacksFrontier.CategoryTheory.Pi.Preadditive
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.ModuleProduct
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite

/-!
# The summands of a simplicial semi-representable ringed site

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`, with
`K_n = {U_{n,i}}_{i ∈ I_n}`. Remark 0D9W equips the total site `(C/K)_total` of the simplicial
site `n ↦ C/K_n` with the sheaf of rings `O = a⁻¹O_C`. Since the localization functor
`j_total : (C/K)_total ⥤ C` is continuous and cocontinuous, `a⁻¹O_C` is the restriction of `O_C`
along `j_total`, and its restriction `O_n` to the component `C/K_n` has sections
`O_n(V → U_{n,i}) = O_C(V)`.

The component `C/K_n` is the disjoint union of the slices `C/U_{n,i}`, so a sheaf of
`O_n`-modules is a family of sheaves of `O_C|_{U_{n,i}}`-modules (Stacks 0D9U), and "this product
decomposition is also inherited by the derived categories of sheaves of modules", as the proof of
Stacks 0DCA puts it: `D(O_n) = ∏_{i ∈ I_n} D(O_{U_{n,i}})`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.structureSheaf`: the sheaf of rings `O = a⁻¹O_C` on
  the total site of the simplicial site of `K`.
* `CategoryTheory.SimplicialSemiRepresentable.summandFunctor`: the inclusion
  `C/U_{n,i} ⥤ C/K_n` of a summand of a component.
* `CategoryTheory.SimplicialSemiRepresentable.summandRestriction`: restriction of
  `O_n`-modules to the summand `C/U_{n,i}`.
* `CategoryTheory.SimplicialSemiRepresentable.summandForgetIso`: the composite of the functors
  of sites `C/U_{n,i} ⥤ C/K_n ⥤ (C/K)_total ⥤ C` is the forgetful functor.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.isEquivalence_pi'_summandRestriction`: the summand
  restrictions identify `Mod(O_n)` with `∏_{i ∈ I_n} Mod(O_{U_{n,i}})`.
* `CategoryTheory.SimplicialSemiRepresentable.isEquivalence_pi'_derivedSummandRestriction`: they
  identify `D(O_n)` with `∏_{i ∈ I_n} D(O_{U_{n,i}})`.

## Implementation notes

The component site of degree `n` has two spellings, the site
`(situation X.J K).componentTopology n` on which `O_n` lives and the componentwise localized
topology `componentwiseTopology X.J K_n` on which Stacks 0D9U is stated, and the two topologies
are equal only propositionally
(`CategoryTheory.SimplicialSemiRepresentable.componentTopology_eq`). They are compared through
`componentSite`, the identity functor read as a continuous functor between them, so that every
restriction functor below is a `SheafOfModules.pushforward` along a continuous functor with a
sectionwise identity ring map, and composites of such are identities on sections.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SemiRepresentable

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **The sheaf of rings `O = a⁻¹O_C` of Remark 0D9W** on the total site of the simplicial site
`n ↦ C/K_n`: the restriction of `O_C` along the localization functor `j_total`, which is
continuous and cocontinuous, so that restriction along it is the inverse image under the
augmentation `a`. -/
def structureSheaf : Sheaf (situation X.J K).totalTopology CommRingCat.{u} :=
  ((totalForget K).sheafPushforwardContinuous CommRingCat.{u} (situation X.J K).totalTopology
    X.J).obj X.O

/-- The ringed topos of the degree-`n` component, with the restriction `O_n` of `O = a⁻¹O_C`. -/
abbrev componentRingedTopos (n : SimplexCategory) : RingedTopos.{u, u, u} :=
  (situation X.J K).componentRingedTopos (structureSheaf X K) n

/-- The sheaf of rings `O_n` over which the sheaves of modules of the degree-`n` component are
taken. -/
abbrev componentRing (n : SimplexCategory) :=
  Stacks.SheafOfModules.Tensor.ringSheaf (componentRingedTopos X K n).O

/-- The componentwise localization `C/K_n`, as the site of the degree-`n` component: the identity
functor between the two spellings of that site. -/
def componentSite (n : SimplexCategory) :
    ComponentOver (K.obj (op n)) ⥤ (componentRingedTopos X K n).C where
  obj V := V
  map f := f

/-- The topology of the degree-`n` component is the componentwise localized topology. -/
theorem componentRingedTopos_J_eq (n : SimplexCategory) :
    (componentRingedTopos X K n).J = componentwiseTopology X.J (K.obj (op n)) :=
  componentTopology_eq X.J K n

/-- `componentSite` is continuous from the componentwise localized topology to the topology of
the degree-`n` component. -/
instance componentSite_isContinuous (n : SimplexCategory) :
    (componentSite X K n).IsContinuous (componentwiseTopology X.J (K.obj (op n)))
      (componentRingedTopos X K n).J := by
  constructor
  intro G
  have h : Presieve.IsSheaf (componentRingedTopos X K n).J G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp G.cond
  change Presieve.IsSheaf (componentwiseTopology X.J (K.obj (op n))) G.obj
  generalize G.obj = P at h ⊢
  rwa [componentRingedTopos_J_eq] at h

/-- `componentSite` is continuous from the topology of the localization `C/K_n`. -/
instance componentSite_isContinuous' (n : SimplexCategory) :
    (componentSite X K n).IsContinuous (X.localization (K.obj (op n))).J
      (componentRingedTopos X K n).J :=
  componentSite_isContinuous X K n

/-- The inverse comparison of the two spellings of the degree-`n` component. -/
def componentSiteInv (n : SimplexCategory) :
    (componentRingedTopos X K n).C ⥤ ComponentOver (K.obj (op n)) where
  obj V := V
  map f := f

/-- `componentSiteInv` is continuous from the topology of the degree-`n` component to the
componentwise localized topology. -/
instance componentSiteInv_isContinuous (n : SimplexCategory) :
    (componentSiteInv X K n).IsContinuous (componentRingedTopos X K n).J
      (componentwiseTopology X.J (K.obj (op n))) := by
  constructor
  intro G
  have h : Presieve.IsSheaf (componentwiseTopology X.J (K.obj (op n))) G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp G.cond
  change Presieve.IsSheaf (componentRingedTopos X K n).J G.obj
  generalize G.obj = P at h ⊢
  rwa [← componentRingedTopos_J_eq] at h

/-- `componentSiteInv` is continuous to the topology of the localization `C/K_n`. -/
instance componentSiteInv_isContinuous' (n : SimplexCategory) :
    (componentSiteInv X K n).IsContinuous (componentRingedTopos X K n).J
      (X.localization (K.obj (op n))).J :=
  componentSiteInv_isContinuous X K n

omit [X.J.toCoverage.HasPullbacks] in
/-- On the component in degree `c`, the localization functor `j_total` is `j_c`, on morphisms. -/
theorem totalForget_map_ι (c : SimplexCategoryᵒᵖ)
    {V W : ((slices K).obj c : Cat)} (f : V ⟶ W) :
    (totalForget K).map ((Grothendieck.ι (slices K) c).map f) = (sliceForget K c).map f := by
  refine (Functor.congr_hom (ι_comp_totalForget K c) f).trans ?_
  exact (congrArg (fun k => k ≫ _ ≫ _) (rfl : eqToHom _ = 𝟙 _)).trans
    ((Category.id_comp _).trans ((congrArg (fun k => _ ≫ k) (rfl : eqToHom _ = 𝟙 _)).trans
      (Category.comp_id _)))

/-- The comparison of the structure sheaf of the localization `C/K_n` of Stacks 0D9U with the
restriction `O_n` of `a⁻¹O_C`: sectionwise the identity. -/
def componentRingMap (n : SimplexCategory) :
    Stacks.SheafOfModules.Tensor.ringSheaf (X.localization (K.obj (op n))).O ⟶
      ((componentSite X K n).sheafPushforwardContinuous RingCat.{u}
        (componentwiseTopology X.J (K.obj (op n))) (componentRingedTopos X K n).J).obj
        (componentRing X K n) :=
  ⟨{ app := fun _ => 𝟙 _
     naturality := fun _ _ f =>
      (Category.comp_id _).trans ((congrArg
        (fun g : _ ⟶ _ => (forget₂ CommRingCat RingCat).map (X.O.obj.map g.op))
        (totalForget_map_ι X K (op n) f.unop).symm).trans (Category.id_comp _).symm) }⟩

/-- The inverse comparison of structure sheaves, sectionwise the identity. -/
def componentRingMapInv (n : SimplexCategory) :
    componentRing X K n ⟶
      ((componentSiteInv X K n).sheafPushforwardContinuous RingCat.{u}
        (componentRingedTopos X K n).J (componentwiseTopology X.J (K.obj (op n)))).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization (K.obj (op n))).O) :=
  ⟨{ app := fun _ => 𝟙 _
     naturality := fun _ _ f =>
      (Category.comp_id _).trans ((congrArg
        (fun g : _ ⟶ _ => (forget₂ CommRingCat RingCat).map (X.O.obj.map g.op))
        (totalForget_map_ι X K (op n) f.unop)).trans (Category.id_comp _).symm) }⟩

/-- Sheaves of `O_n`-modules are sheaves of modules over the structure sheaf of the localization
`C/K_n` of Stacks 0D9U. -/
def componentModulesEquivalence (n : SimplexCategory) :
    SheafOfModules.{u} (componentRing X K n) ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.localization (K.obj (op n))).O) :=
  { functor := SheafOfModules.pushforward (J := componentwiseTopology X.J (K.obj (op n)))
      (K := (componentRingedTopos X K n).J) (componentRingMap X K n)
    inverse := SheafOfModules.pushforward (J := (componentRingedTopos X K n).J)
      (K := componentwiseTopology X.J (K.obj (op n))) (componentRingMapInv X K n)
    unitIso := NatIso.ofComponents (fun _ => (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => rfl)) fun _ => rfl
    counitIso := NatIso.ofComponents (fun _ => (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => rfl)) fun _ => rfl
    functor_unitIso_comp _ := rfl }

/-- The inclusion `C/U_{n,i} ⥤ C/K_n` of the `i`-th summand of the degree-`n` component. -/
def summandFunctor (n : SimplexCategory) (i : (K.obj (op n)).I) :
    Over ((K.obj (op n)).obj i) ⥤ (componentRingedTopos X K n).C :=
  CategoryTheory.Sigma.incl (C := fun j : (K.obj (op n)).I => Over ((K.obj (op n)).obj j)) i ⋙
    componentSite X K n

/-- The inclusion of a summand `C/U_{n,i} ⥤ C/K_n` is continuous. -/
instance summandFunctor_isContinuous (n : SimplexCategory) (i : (K.obj (op n)).I) :
    (summandFunctor X K n i).IsContinuous (X.J.over ((K.obj (op n)).obj i))
      (componentRingedTopos X K n).J :=
  haveI := incl_isContinuous X.J (K.obj (op n)) i
  Functor.isContinuous_comp _ _ _ (componentwiseTopology X.J (K.obj (op n))) _

/-- **The composite `C/U_{n,i} ⥤ C/K_n ⥤ (C/K)_total ⥤ C` is the forgetful functor**: it is so on
objects, and on arrows by `totalForget_map_ι`. -/
def summandForgetIso (n : SimplexCategory) (i : (K.obj (op n)).I) :
    (summandFunctor X K n i ⋙ (situation X.J K).componentFunctor n) ⋙ totalForget K ≅
      Over.forget ((K.obj (op n)).obj i) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {_ _} f ↦
    ((Category.comp_id _).trans
      (totalForget_map_ι X K (op n) (CategoryTheory.Sigma.SigmaHom.mk f))).trans
        (Category.id_comp _).symm

/-- The components of the inverse of `summandForgetIso` are identities. -/
theorem summandForgetIso_inv_app (n : SimplexCategory) (i : (K.obj (op n)).I)
    (W : Over ((K.obj (op n)).obj i)) :
    (summandForgetIso X K n i).inv.app W = 𝟙 W.left :=
  rfl

/-- The comparison of the restriction of `O_n` to the summand `C/U_{n,i}` with `O_C|_{U_{n,i}}`:
sectionwise the identity. -/
def summandRingMap (n : SimplexCategory) (i : (K.obj (op n)).I) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((K.obj (op n)).obj i) ⟶
      ((summandFunctor X K n i).sheafPushforwardContinuous RingCat.{u}
        (X.J.over ((K.obj (op n)).obj i)) (componentRingedTopos X K n).J).obj
        (componentRing X K n) :=
  ⟨{ app := fun _ => 𝟙 _
     naturality := fun _ _ f =>
      (Category.comp_id _).trans ((congrArg
        (fun g : _ ⟶ _ => (forget₂ CommRingCat RingCat).map (X.O.obj.map g.op))
        (totalForget_map_ι X K (op n) (CategoryTheory.Sigma.SigmaHom.mk f.unop)).symm).trans
          (Category.id_comp _).symm) }⟩

/-- **Restriction of `O_n`-modules to the summand `C/U_{n,i}`.** -/
def summandRestriction (n : SimplexCategory) (i : (K.obj (op n)).I) :
    SheafOfModules.{u} (componentRing X K n) ⥤
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((K.obj (op n)).obj i)) :=
  SheafOfModules.pushforward (summandRingMap X K n i)

/-- The summand restrictions are the componentwise restrictions of Stacks 0D9U, after the
comparison of the two spellings of the component. -/
def pi'SummandRestrictionIso (n : SimplexCategory) :
    Functor.pi' (summandRestriction X K n) ≅
      (componentModulesEquivalence X K n).functor ⋙
        RingedSite.componentwiseModuleRestriction' X (K.obj (op n)) :=
  NatIso.ofComponents (fun M => Pi.isoMk fun i =>
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U => Iso.refl (((summandRestriction X K n i).obj M).val.obj U))
        fun _ _ _ => rfl)) fun f => by
    funext i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

/-- **Stacks 0D9U for the component `C/K_n`.** The summand restrictions identify `Mod(O_n)` with
`∏_{i ∈ I_n} Mod(O_{U_{n,i}})`. -/
instance isEquivalence_pi'_summandRestriction (n : SimplexCategory) :
    (Functor.pi' (summandRestriction X K n)).IsEquivalence := by
  have h₁ : (RingedSite.componentwiseModuleRestriction'.{u, u, u, u, u} X
      (K.obj (op n))).IsEquivalence := by
    obtain ⟨e, he⟩ := RingedSite.moduleSheavesProductEquivalence'.{u, u, u, u, u} X (K.obj (op n))
    rw [← he]
    exact e.isEquivalence_functor
  have h₂ := (componentModulesEquivalence X K n).isEquivalence_functor
  have : ((componentModulesEquivalence X K n).functor ⋙
      RingedSite.componentwiseModuleRestriction'.{u, u, u, u, u} X (K.obj (op n))).IsEquivalence :=
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h₂ h₁
  exact @Functor.isEquivalence_of_iso _ _ _ _ _ _ (pi'SummandRestrictionIso X K n).symm this

/-- Restriction to a summand is additive. -/
instance summandRestriction_additive (n : SimplexCategory) (i : (K.obj (op n)).I) :
    (summandRestriction X K n i).Additive where
  map_add := rfl

/-- Restriction to a summand preserves finite limits: it is a projection of an equivalence. -/
instance summandRestriction_preservesFiniteLimits (n : SimplexCategory) (i : (K.obj (op n)).I) :
    PreservesFiniteLimits (summandRestriction X K n i) :=
  haveI := Pi.preservesFiniteLimits_eval
    (A := fun i => SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((K.obj (op n)).obj i))) i
  inferInstanceAs (PreservesFiniteLimits (Functor.pi' (summandRestriction X K n) ⋙ Pi.eval _ i))

/-- Restriction to a summand preserves finite colimits: it is a projection of an equivalence. -/
instance summandRestriction_preservesFiniteColimits (n : SimplexCategory)
    (i : (K.obj (op n)).I) : PreservesFiniteColimits (summandRestriction X K n i) :=
  haveI := Pi.preservesFiniteColimits_eval
    (A := fun i => SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((K.obj (op n)).obj i))) i
  inferInstanceAs (PreservesFiniteColimits (Functor.pi' (summandRestriction X K n) ⋙ Pi.eval _ i))

attribute [local instance] HasDerivedCategory.standard

/-- **The product decomposition of the derived category of a component.** The derived summand
restrictions identify `D(O_n)` with `∏_{i ∈ I_n} D(O_{U_{n,i}})`. -/
instance isEquivalence_pi'_derivedSummandRestriction (n : SimplexCategory) :
    (Functor.pi' fun i => (summandRestriction X K n i).mapDerivedCategory).IsEquivalence :=
  Functor.isEquivalence_pi'_mapDerivedCategory (summandRestriction X K n)

end CategoryTheory.SimplicialSemiRepresentable
