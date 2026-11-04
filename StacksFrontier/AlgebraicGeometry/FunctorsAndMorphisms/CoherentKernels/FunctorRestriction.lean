module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentKernels.Defs
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.DirectSums
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.Exactness
public import StacksFrontier.CategoryTheory.KanExtension.Extend

/-!
# Functors on coherent modules and their extensions to quasi-coherent modules

Let `X` be a Noetherian scheme. A functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` which commutes with filtered
colimits is determined by its restriction to `Coh(𝒪_X)`, and so are the natural transformations
between two such functors. This file records the consequences used for [Stacks, Tag 0FZN]:

* natural transformations between filtered-colimit-preserving functors are exactly the natural
  transformations between their restrictions to the coherent modules;
* the extension of [Stacks, Tag 0FZL] of a `k`-linear functor is `k`-linear;
* an exact functor commuting with arbitrary direct sums commutes with all colimits, in
  particular with filtered colimits;
* restriction to the coherent modules is a fully faithful functor from the `k`-linear exact
  functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` commuting with direct sums and sending coherent modules to
  coherent modules, to the `k`-linear exact functors `Coh(𝒪_X) ⥤ Coh(𝒪_Y)`, and every functor of
  the latter kind is the restriction of its extension.

## Main definitions

* `AlgebraicGeometry.CoherentKernels.PreservesCoherent`: a functor of quasi-coherent modules
  sending coherent modules to coherent modules.
* `AlgebraicGeometry.CoherentKernels.coherentRestriction`: the restriction of such a functor to
  the coherent modules.
* `AlgebraicGeometry.CoherentKernels.coherentRestrictionFunctor`: restriction, as a functor from
  the exact functors of [Stacks, Tag 0FZH] preserving coherence to the exact functors of
  [Stacks, Tag 0FZN].

## Main results

* `AlgebraicGeometry.CoherentKernels.existsUnique_natTrans_of_whiskerLeft`: natural
  transformations are determined by, and extend from, the coherent modules.
* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.linear`: the extension of a
  linear functor is linear.
* `AlgebraicGeometry.CoherentKernels.preservesFilteredColimits_of_exactLinearCoproductFunctor`.
* `AlgebraicGeometry.CoherentKernels.fullyFaithfulCoherentRestrictionFunctor` and
  `AlgebraicGeometry.CoherentKernels.coherentRestrictionFunctor_essSurj`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (CoherentModules)
open AlgebraicGeometry.CoherentModuleFunctors

universe u

namespace AlgebraicGeometry.CoherentKernels

/-! ### Natural transformations are determined on the coherent modules -/

section NatTrans

variable {X : Scheme.{u}} [IsNoetherian X] {D : Type*} [Category D]

/-- **Natural transformations between filtered-colimit-preserving functors out of `QCoh(𝒪_X)`
are those between their restrictions to `Coh(𝒪_X)`.** For `X` Noetherian every quasi-coherent
module is a filtered colimit of coherent ones, which are finitely presentable objects. -/
theorem existsUnique_natTrans_of_whiskerLeft
    (G₁ G₂ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ D)
    [PreservesFilteredColimitsOfSize.{u, u} G₁]
    (β : coherentToQuasicoherent X ⋙ G₁ ⟶ coherentToQuasicoherent X ⋙ G₂) :
    ∃! φ : G₁ ⟶ G₂, Functor.whiskerLeft (coherentToQuasicoherent X) φ = β := by
  have : EssentiallySmall.{u} (coherentProperty X).FullSubcategory :=
    essentiallySmall_coherentProperty X
  have hcompact : coherentProperty X ≤
      ObjectProperty.isFinitelyPresentable.{u}
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    fun M hM => isFinitelyPresentable_of_isCoherent X M hM
  let β' : (coherentProperty X).ι ⋙ G₁ ⟶ (coherentProperty X).ι ⋙ G₂ :=
    { app := fun A => β.app ((coherentSubcategoryEquivalence X).functor.obj A)
      naturality := fun A B f => β.naturality ((coherentSubcategoryEquivalence X).functor.map f) }
  obtain ⟨φ, hφ, hu⟩ := ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits
    (coherentProperty X) hcompact (coherentProperty_ind X) G₁ G₂ β'
  refine ⟨φ, ?_, fun ψ hψ => hu ψ ?_⟩
  · ext M
    exact congrArg (fun τ => τ.app ((coherentSubcategoryEquivalence X).inverse.obj M)) hφ
  · ext A
    exact congrArg (fun τ => τ.app ((coherentSubcategoryEquivalence X).functor.obj A)) hψ

/-- Two natural transformations between functors out of `QCoh(𝒪_X)` commuting with filtered
colimits agree as soon as they agree on the coherent modules. -/
theorem natTrans_ext_of_whiskerLeft
    {G₁ G₂ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ D}
    [PreservesFilteredColimitsOfSize.{u, u} G₁] {φ ψ : G₁ ⟶ G₂}
    (h : Functor.whiskerLeft (coherentToQuasicoherent X) φ =
      Functor.whiskerLeft (coherentToQuasicoherent X) ψ) : φ = ψ :=
  (existsUnique_natTrans_of_whiskerLeft G₁ G₂ _).unique h rfl

end NatTrans

/-! ### Linearity of the extension -/

section Linear

variable {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))} [IsNoetherian X.left]

/-- In a linear category, `r • 𝟙` commutes with every morphism. -/
private theorem smul_id_comm {C : Type*} [Category C] [Preadditive C] [Linear R C] {N N' : C}
    (f : N ⟶ N') (r : R) : f ≫ (r • 𝟙 N') = (r • 𝟙 N) ≫ f := by
  simp

/-- **The extension of a linear functor is linear.** For `r : R` the two natural endomorphisms
`M ↦ E(r • 𝟙_M)` and `M ↦ r • 𝟙_{E M}` of the extension `E` agree on the coherent modules, where
`E` is `F` and `F` is linear, so they agree. -/
theorem _root_.AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.linear
    {F : CoherentModules X.left.ringCatSheaf ⥤ CoherentModules Y.left.ringCatSheaf}
    (E : FilteredColimitExtension X.left Y.left F)
    (hF : letI := coherentModulesLinear R X
      letI := coherentModulesLinear R Y
      F.Linear R) :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    E.functor.Linear R := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  let iX : Linear R (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory :=
    Linear.fullSubcategory _
  let iY : Linear R (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory :=
    Linear.fullSubcategory _
  let := coherentModulesLinear R X
  let := coherentModulesLinear R Y
  rw [Functor.linear_iff]
  intro M r
  let α : E.functor ⟶ E.functor :=
    { app := fun N => E.functor.map (r • 𝟙 N)
      naturality := fun N N' f => (E.functor.map_comp _ _).symm.trans
        ((congrArg E.functor.map (smul_id_comm f r)).trans (E.functor.map_comp _ _)) }
  let β : E.functor ⟶ E.functor :=
    { app := fun N => r • 𝟙 (E.functor.obj N)
      naturality := fun N N' f => smul_id_comm _ r }
  have hαβ : α = β := by
    refine natTrans_ext_of_whiskerLeft (X := X.left) ?_
    ext1
    funext N
    have hnat := E.iso.hom.naturality (r • 𝟙 N)
    have hlin : F.map (r • 𝟙 N) = r • 𝟙 (F.obj N) :=
      (Functor.linear_iff R F).mp hF N r
    show E.functor.map ((coherentToQuasicoherent X.left).map (r • 𝟙 N)) =
      r • 𝟙 (E.functor.obj ((coherentToQuasicoherent X.left).obj N))
    have hinc' : (coherentToQuasicoherent Y.left).map (F.map (r • 𝟙 N)) =
        r • 𝟙 ((coherentToQuasicoherent Y.left).obj (F.obj N)) :=
      (congrArg (coherentToQuasicoherent Y.left).map hlin).trans rfl
    have hnat' : E.functor.map ((coherentToQuasicoherent X.left).map (r • 𝟙 N)) ≫
        E.iso.hom.app N = E.iso.hom.app N ≫
          (r • 𝟙 ((coherentToQuasicoherent Y.left).obj (F.obj N))) :=
      hnat.trans (congrArg (E.iso.hom.app N ≫ ·) hinc')
    exact ((E.iso.app N).cancel_iso_hom_right _ _).1 (hnat'.trans (smul_id_comm _ r))
  exact congrArg (fun τ : E.functor ⟶ E.functor => τ.app M) hαβ

end Linear

/-! ### Exact functors commuting with direct sums commute with all colimits -/

/-- **An exact functor of quasi-coherent modules commuting with arbitrary direct sums commutes
with all colimits**, in particular with filtered colimits: colimits are built from coequalizers
and coproducts. -/
theorem preservesColimitsOfSize_of_exactLinearCoproductFunctor
    {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))}
    {G : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory}
    (hG : exactLinearCoproductFunctor R X Y G) : PreservesColimitsOfSize.{u, u} G := by
  have := hasColimitsOfSize_quasicoherent X.left
  have : PreservesFiniteColimits G := ((exactFunctor_iff G).mp hG.2.1).2
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) G := hG.2.2
  exact preservesColimits_of_preservesCoequalizers_and_coproducts.{u} G

/-- An exact functor of quasi-coherent modules commuting with arbitrary direct sums commutes
with filtered colimits. -/
theorem preservesFilteredColimits_of_exactLinearCoproductFunctor
    {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))}
    {G : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory}
    (hG : exactLinearCoproductFunctor R X Y G) : PreservesFilteredColimitsOfSize.{u, u} G :=
  have := preservesColimitsOfSize_of_exactLinearCoproductFunctor hG
  inferInstance

/-! ### Restriction to the coherent modules -/

section Restriction

variable {X Y : Scheme.{u}}

/-- A functor of quasi-coherent modules **preserves coherence** when it sends coherent modules
to coherent modules. -/
def PreservesCoherent :
    ObjectProperty ((SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :=
  fun G => ∀ M : CoherentModules X.ringCatSheaf,
    (G.obj ((coherentToQuasicoherent X).obj M)).obj.IsCoherent

/-- The restriction to the coherent modules of a functor of quasi-coherent modules which
preserves coherence. -/
def coherentRestriction
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (hG : PreservesCoherent G) :
    CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf :=
  ObjectProperty.lift _ (coherentToQuasicoherent X ⋙ G ⋙
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι) hG

/-- The restriction of `G`, followed by the inclusion of the coherent modules, is `G` on the
coherent modules. -/
theorem coherentRestriction_comp
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (hG : PreservesCoherent G) :
    coherentRestriction G hG ⋙ coherentToQuasicoherent Y = coherentToQuasicoherent X ⋙ G :=
  rfl

end Restriction

/-! ### Restriction of exact functors to the coherent modules -/

section RestrictionFunctor

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- A functor is exact if its composite with a functor reflecting finite limits and colimits is. -/
private theorem exactFunctor_of_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) [ReflectsFiniteLimits G] [ReflectsFiniteColimits G]
    (h : exactFunctor _ _ (F ⋙ G)) : exactFunctor _ _ F := by
  obtain ⟨h₁, h₂⟩ := (exactFunctor_iff _).mp h
  exact (exactFunctor_iff _).mpr
    ⟨preservesFiniteLimits_of_reflects_of_preserves F G,
      preservesFiniteColimits_of_reflects_of_preserves F G⟩

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` preserves finite limits and finite colimits. -/
theorem exactFunctor_coherentToQuasicoherent (Z : Scheme.{u}) :
    exactFunctor _ _ (coherentToQuasicoherent Z) := by
  have hι : exactFunctor _ _
      (ObjectProperty.ι (fun M : SheafOfModules.{u} Z.ringCatSheaf => M.IsCoherent)) :=
    (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩
  exact exactFunctor_of_comp _ (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι hι

/-- The restriction to the coherent modules of a `k`-linear exact functor of quasi-coherent
modules preserving coherence is `k`-linear and exact. -/
theorem exactLinearCoherentFunctor_coherentRestriction
    {G : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory}
    (hG : exactLinearCoproductFunctor k X Y G) (hc : PreservesCoherent G) :
    exactLinearCoherentFunctor k X Y (coherentRestriction G hc) := by
  let : Linear k (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear k X
  let : Linear k (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear k Y
  let : Linear k (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory :=
    Linear.fullSubcategory _
  let : Linear k (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory :=
    Linear.fullSubcategory _
  let := coherentModulesLinear k X
  let := coherentModulesLinear k Y
  have hlin : G.Linear k := hG.1.2
  refine ⟨⟨fun {M N} f r => ?_⟩, ?_⟩
  · refine ObjectProperty.hom_ext _ ?_
    show (G.map ((coherentToQuasicoherent X.left).map (r • f))).hom =
      (r • G.map ((coherentToQuasicoherent X.left).map f)).hom
    exact congrArg InducedCategory.Hom.hom
      (Functor.Linear.map_smul (F := G) ((coherentToQuasicoherent X.left).map f) r)
  · obtain ⟨h₁, h₂⟩ := (exactFunctor_iff _).mp (exactFunctor_coherentToQuasicoherent X.left)
    obtain ⟨h₃, h₄⟩ := (exactFunctor_iff _).mp hG.2.1
    refine exactFunctor_of_comp _ (coherentToQuasicoherent Y.left) ?_
    rw [coherentRestriction_comp]
    exact (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- The `k`-linear exact functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` commuting with direct sums which
preserve coherence. -/
abbrev exactLinearCoproductCoherentFunctor :
    ObjectProperty ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory) :=
  exactLinearCoproductFunctor k X Y ⊓ PreservesCoherent

/-- **Restriction to the coherent modules**, from the `k`-linear exact functors of
quasi-coherent modules commuting with direct sums and preserving coherence to the `k`-linear
exact functors of coherent modules. -/
def coherentRestrictionFunctor :
    (exactLinearCoproductCoherentFunctor k X Y).FullSubcategory ⥤
      (exactLinearCoherentFunctor k X Y).FullSubcategory where
  obj G := ⟨coherentRestriction G.obj G.property.2,
    exactLinearCoherentFunctor_coherentRestriction k X Y G.property.1 G.property.2⟩
  map {G G'} φ := ObjectProperty.homMk
    { app := fun M => ObjectProperty.homMk
        (φ.hom.app ((coherentToQuasicoherent X.left).obj M)).hom
      naturality := fun M N f => ObjectProperty.hom_ext _ (by
        change (G.obj.map ((coherentToQuasicoherent X.left).map f) ≫
            φ.hom.app ((coherentToQuasicoherent X.left).obj N)).hom =
          (φ.hom.app ((coherentToQuasicoherent X.left).obj M) ≫
            G'.obj.map ((coherentToQuasicoherent X.left).map f)).hom
        exact congrArg InducedCategory.Hom.hom
          (φ.hom.naturality ((coherentToQuasicoherent X.left).map f))) }

/-- The restriction functor followed by forgetting coherence of the values is whiskering with
the inclusion of the coherent modules. -/
theorem coherentRestrictionFunctor_map_app
    {G G' : (exactLinearCoproductCoherentFunctor k X Y).FullSubcategory} (φ : G ⟶ G')
    (M : CoherentModules X.left.ringCatSheaf) :
    (coherentToQuasicoherent Y.left).map (((coherentRestrictionFunctor k X Y).map φ).hom.app M) =
      φ.hom.app ((coherentToQuasicoherent X.left).obj M) :=
  rfl

variable [IsNoetherian X.left]

/-- **Restriction to the coherent modules is fully faithful.** The functors commute with
filtered colimits, so natural transformations are determined by, and extend from, their values
on the coherent modules. -/
def fullyFaithfulCoherentRestrictionFunctor :
    (coherentRestrictionFunctor k X Y).FullyFaithful where
  preimage {G G'} β :=
    have := preservesFilteredColimits_of_exactLinearCoproductFunctor G.property.1
    ObjectProperty.homMk (existsUnique_natTrans_of_whiskerLeft G.obj G'.obj
      (Functor.whiskerRight β.hom (coherentToQuasicoherent Y.left))).choose
  map_preimage {G G'} β := by
    have := preservesFilteredColimits_of_exactLinearCoproductFunctor G.property.1
    have h := (existsUnique_natTrans_of_whiskerLeft G.obj G'.obj
      (Functor.whiskerRight β.hom (coherentToQuasicoherent Y.left))).choose_spec.1
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun M => ?_))
    refine (coherentToQuasicoherent Y.left).map_injective ?_
    exact congrArg (fun τ => τ.app M) h
  preimage_map {G G'} φ := by
    have := preservesFilteredColimits_of_exactLinearCoproductFunctor G.property.1
    refine ObjectProperty.hom_ext _ ?_
    exact ((existsUnique_natTrans_of_whiskerLeft G.obj G'.obj
      (Functor.whiskerRight ((coherentRestrictionFunctor k X Y).map φ).hom
        (coherentToQuasicoherent Y.left))).unique
      (existsUnique_natTrans_of_whiskerLeft G.obj G'.obj _).choose_spec.1 rfl)

variable [IsNoetherian Y.left]

/-- The extension of [Stacks, Tag 0FZL] of a `k`-linear exact functor of coherent modules is a
`k`-linear exact functor of quasi-coherent modules commuting with direct sums and preserving
coherence. -/
theorem exactLinearCoproductCoherentFunctor_filteredColimitExtension
    (F : (exactLinearCoherentFunctor k X Y).FullSubcategory) :
    exactLinearCoproductCoherentFunctor k X Y
      (filteredColimitExtension X.left Y.left F.obj).functor := by
  let E := filteredColimitExtension X.left Y.left F.obj
  have : F.obj.Additive := exactFunctor_le_additiveFunctor _ _ F.obj F.property.2
  refine ⟨⟨⟨E.additive, E.linear F.property.1⟩, E.exactFunctor F.property.2,
    E.preservesCoproducts⟩, fun M => ?_⟩
  exact ObjectProperty.prop_of_iso (P := fun N : SheafOfModules.{u} Y.left.ringCatSheaf =>
      N.IsCoherent)
    ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι.mapIso (E.iso.app M)).symm
    (F.obj.obj M).property

/-- The extension of a `k`-linear exact functor of coherent modules, as an object of the source
of `coherentRestrictionFunctor`. -/
def extensionObj (F : (exactLinearCoherentFunctor k X Y).FullSubcategory) :
    (exactLinearCoproductCoherentFunctor k X Y).FullSubcategory :=
  ⟨_, exactLinearCoproductCoherentFunctor_filteredColimitExtension k X Y F⟩

/-- **A `k`-linear exact functor of coherent modules is the restriction of its extension.** -/
def coherentRestrictionExtensionIso (F : (exactLinearCoherentFunctor k X Y).FullSubcategory) :
    coherentRestriction (extensionObj k X Y F).obj (extensionObj k X Y F).property.2 ≅ F.obj :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι.mapIso
        ((filteredColimitExtension X.left Y.left F.obj).iso.app M)))
    (fun {M N} f => ObjectProperty.hom_ext _ (by
      change ((filteredColimitExtension X.left Y.left F.obj).functor.map
          ((coherentToQuasicoherent X.left).map f) ≫
          (filteredColimitExtension X.left Y.left F.obj).iso.hom.app N).hom =
        ((filteredColimitExtension X.left Y.left F.obj).iso.hom.app M ≫
          (coherentToQuasicoherent Y.left).map (F.obj.map f)).hom
      exact congrArg InducedCategory.Hom.hom
        ((filteredColimitExtension X.left Y.left F.obj).iso.hom.naturality f)))

/-- **Every `k`-linear exact functor of coherent modules is the restriction of its
extension.** -/
theorem coherentRestrictionFunctor_essSurj : (coherentRestrictionFunctor k X Y).EssSurj :=
  ⟨fun F => ⟨extensionObj k X Y F,
    ⟨ObjectProperty.isoMk _ (coherentRestrictionExtensionIso k X Y F)⟩⟩⟩

end RestrictionFunctor

end AlgebraicGeometry.CoherentKernels

end
