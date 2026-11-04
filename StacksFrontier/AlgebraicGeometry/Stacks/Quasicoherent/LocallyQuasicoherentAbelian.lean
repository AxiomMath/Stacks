module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor

/-!
# Restriction of étale sheaves of modules to a small étale site is exact (Stacks 06WJ)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying
over a scheme `U`.  The restriction `F ↦ x^*F|_{U_ét}` of Stacks 06WJ carries étale sheaves of
`𝒪_𝒳`-modules to sheaves of modules on the small étale site of `U`.  This file packages it as a
functor between the two categories of sheaves of modules and proves that it commutes with limits
and with colimits.

## Main definitions

* `AlgebraicGeometry.Stack.restrictSheafToSmallEtale`: the restriction of Stacks 06WJ as a
  functor `Mod(𝒳_ét, 𝒪_𝒳) ⥤ Mod(U_ét, 𝒪_U)`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff`: a sheaf of modules on `𝒳_ét` is locally
  quasi-coherent exactly when all its restrictions are quasi-coherent.
* `AlgebraicGeometry.Stack.preservesLimitsOfShape_restrictSheafToSmallEtale`: the restriction
  commutes with limits, which are computed on sections on both sides.
* `AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale`: the restriction
  commutes with colimits.
* `AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_isLocallyQuasicoherent`,
  `AlgebraicGeometry.Stack.isClosedUnderKernels_isLocallyQuasicoherent`,
  `AlgebraicGeometry.Stack.isClosedUnderCokernels_isLocallyQuasicoherent` and
  `AlgebraicGeometry.Stack.isClosedUnderFiniteProducts_isLocallyQuasicoherent`: consequently local
  quasi-coherence is closed under colimits, kernels, cokernels and finite products, by the
  corresponding closure properties of quasi-coherent modules on small étale sites (Descent,
  Lemma 0GNB).

## Implementation notes

Colimits of sheaves of modules are sheafifications of colimits of presheaves of modules.  The
restriction commutes with colimits of presheaves, being restriction along a functor followed by
a change of scalars, and it commutes with sheafification because the restricting functor of
Stacks 06W1 is cocontinuous as well as continuous
(`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`).  The comparison is
packaged as the natural transformation `restrictSheafificationComparison`, obtained from the
sheafification adjunction, whose components are the isomorphisms of that file.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m j jv

namespace CategoryTheory

/-- A functor out of a reflective subcategory preserves colimits of a shape as soon as its
composite with the reflector does, provided the ambient category has colimits of that shape: a
diagram of the subcategory is the reflection of its image, and the reflector carries a colimit
of that image to a colimit. -/
theorem Adjunction.preservesColimitsOfShape_of_comp_reflector {P Q T : Type*} [Category* P]
    [Category* Q] [Category* T] {L : P ⥤ Q} {i : Q ⥤ P} (adj : L ⊣ i) [i.Full] [i.Faithful]
    (G : Q ⥤ T) (K : Type*) [Category* K] [HasColimitsOfShape K P]
    [PreservesColimitsOfShape K (L ⋙ G)] : PreservesColimitsOfShape K G := by
  have : PreservesColimitsOfShape K L := adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  refine ⟨fun {D} => ?_⟩
  have e : (D ⋙ i) ⋙ L ≅ D :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft D (asIso adj.counit) ≪≫ D.rightUnitor
  have hc : IsColimit (L.mapCocone (colimit.cocone (D ⋙ i))) :=
    isColimitOfPreserves L (colimit.isColimit _)
  have hc' : IsColimit (G.mapCocone (L.mapCocone (colimit.cocone (D ⋙ i)))) :=
    isColimitOfPreserves (L ⋙ G) (colimit.isColimit _)
  have : PreservesColimit ((D ⋙ i) ⋙ L) G := preservesColimit_of_preserves_colimit_cocone hc hc'
  exact preservesColimit_of_iso_diagram G e

end CategoryTheory

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Stacks 06WJ.** The restriction `F ↦ x^*F|_{U_ét}` to the small étale site of the scheme
below an object `x`, as a functor from the étale sheaves of modules on `𝒳` to the sheaves of
modules on that small étale site.  On underlying presheaves of modules it is
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor`, and the restriction of an étale
sheaf is a sheaf by `AlgebraicGeometry.Stack.restrictModuleToSmallEtale_isSheaf`. -/
@[reducible] noncomputable def restrictSheafToSmallEtale (x : 𝒳) :
    SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)) ⥤
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) where
  obj F := ⟨(restrictModuleToSmallEtaleFunctor B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).obj F.val,
    restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F.val F.isSheaf⟩
  map f := ⟨(restrictModuleToSmallEtaleFunctor B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).map f.val⟩
  map_id F := SheafOfModules.hom_ext
    ((restrictModuleToSmallEtaleFunctor B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).map_id F.val)
  map_comp f g := SheafOfModules.hom_ext
    ((restrictModuleToSmallEtaleFunctor B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).map_comp f.val g.val)

/-- The restriction functor followed by the forgetful functor to presheaves of modules is the
forgetful functor followed by the restriction of presheaves of modules. -/
theorem restrictSheafToSmallEtale_comp_forget (x : 𝒳) :
    restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x ⋙ SheafOfModules.forget _ =
      SheafOfModules.forget _ ⋙ restrictModuleToSmallEtaleFunctor B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) x :=
  rfl

/-- **Stacks 06WJ, read on sheaves of modules.** An étale sheaf of modules on `𝒳` is locally
quasi-coherent exactly when its restriction to the small étale site of the scheme below every
object is quasi-coherent; the sheaf condition of Stacks 06WJ is part of being an étale sheaf. -/
theorem isLocallyQuasicoherent_iff
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsLocallyQuasicoherent B E h S hS p hp F.val ↔
      ∀ x : 𝒳, ((restrictSheafToSmallEtale B E h S hS p hp x).obj F).IsQuasicoherentOnSite :=
  ⟨fun hF x => (hF.2 x).choose_spec, fun H => ⟨F.isSheaf, fun x => ⟨_, H x⟩⟩⟩

section Limits

variable (K : Type j) [Category.{jv} K] [HasLimitsOfShape K (Type u)]

/-- Restriction of presheaves of modules to the small étale site preserves limits: it is
restriction along a functor, which is a reindexing after evaluation, followed by a change of
scalars, which changes nothing on sections. -/
instance preservesLimitsOfShape_restrictModuleToSmallEtaleFunctor (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    PreservesLimitsOfShape K
      (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x) := by
  constructor
  intro D
  constructor
  intro c hc
  have hsmall : ∀ X, Small.{u} (((D ⋙
      restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x) ⋙
        PresheafOfModules.evaluation _ X) ⋙ forget _).sections := fun X =>
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have hsmall' : ∀ Y, Small.{u} ((D ⋙ PresheafOfModules.evaluation _ Y) ⋙ forget _).sections :=
    fun Y => (Types.hasLimit_iff_small_sections _).mp inferInstance
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X => ?_⟩
  have := isEquivalence_overPost B S hS p hp x
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  exact isLimitOfPreserves (ModuleCat.restrictScalars.{u}
    ((localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app X).hom)
      (isLimitOfPreserves (PresheafOfModules.evaluation
        (ringStructureSheafCore B S hS p hp τ hτ).obj (q.op.obj X)) hc)

/-- **The restriction of étale sheaves of modules to a small étale site preserves limits**, which
are computed on underlying presheaves of modules on both sides. -/
instance preservesLimitsOfShape_restrictSheafToSmallEtale (x : 𝒳)
    [PreservesLimitsOfShape K (SheafOfModules.forget.{u} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)))] :
    PreservesLimitsOfShape K (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x) := by
  have : PreservesLimitsOfShape K (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x ⋙
      SheafOfModules.forget _) := by
    rw [restrictSheafToSmallEtale_comp_forget]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.forget _)

/-- The restriction of étale sheaves of modules to a small étale site is left exact. -/
instance preservesFiniteLimits_restrictSheafToSmallEtale (x : 𝒳) :
    PreservesFiniteLimits (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x) :=
  ⟨fun _ _ _ => inferInstance⟩

end Limits

section Colimits

variable [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheafification of presheaves of modules on the associated étale site of `𝒳`. -/
noncomputable abbrev etaleSheafification :
    PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)) :=
  PresheafOfModules.sheafification.{u}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)

/-- The sheafification adjunction of the associated étale site of `𝒳`. -/
noncomputable abbrev etaleSheafificationAdjunction :
    etaleSheafification B S hS p hp ⊣ SheafOfModules.forget _ :=
  PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)

/-- Sheafification of presheaves of modules on the small étale site of the scheme below `x`. -/
noncomputable abbrev smallEtaleSheafification (x : 𝒳) :
    PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) :=
  PresheafOfModules.sheafification.{u}
    (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)

/-- The sheafification adjunction of the small étale site of the scheme below `x`. -/
noncomputable abbrev smallEtaleSheafificationAdjunction (x : 𝒳) :
    smallEtaleSheafification B E h S hS p x ⊣ SheafOfModules.forget _ :=
  PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)

/-- The unit of the sheafification adjunction of the associated étale site of `𝒳`, with its
target written as the underlying presheaf of the sheafification. -/
noncomputable def etaleSheafificationUnit
    (M : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    M ⟶ ((etaleSheafification B S hS p hp).obj M).val :=
  (etaleSheafificationAdjunction B S hS p hp).unit.app M

/-- Naturality of `etaleSheafificationUnit`: for a morphism `f : M ⟶ N` of presheaves of modules,
`f` followed by the unit at `N` equals the unit at `M` followed by the sheafification of `f`. -/
theorem etaleSheafificationUnit_naturality
    {M N : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj} (f : M ⟶ N) :
    f ≫ etaleSheafificationUnit B S hS p hp N =
      etaleSheafificationUnit B S hS p hp M ≫ ((etaleSheafification B S hS p hp).map f).val :=
  (etaleSheafificationAdjunction B S hS p hp).unit.naturality f

/-- The component at `M` of `restrictSheafificationComparison`: the transpose of the restriction
of the sheafification unit. -/
noncomputable def restrictSheafificationComparisonApp (x : 𝒳)
    (M : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    (smallEtaleSheafification B E h S hS p x).obj
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) x).obj M) ⟶
      (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj
        ((etaleSheafification B S hS p hp).obj M) :=
  ((smallEtaleSheafificationAdjunction B E h S hS p x).homEquiv _
      ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj
        ((etaleSheafification B S hS p hp).obj M))).symm
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).map (etaleSheafificationUnit B S hS p hp M))

/-- The component of `restrictSheafificationComparison` is the isomorphism
`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso` of Stacks 06W1. -/
theorem isIso_restrictSheafificationComparisonApp (x : 𝒳)
    (M : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsIso (restrictSheafificationComparisonApp B E h S hS p hp x M) := by
  let hx := isEquivalence_overPost B S hS p hp x
  let K := associatedTopology B S hS p (etaleTopology B)
  let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  obtain ⟨hq₁, hq₂⟩ := isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  have hqc : q.IsContinuous J K := hq₁
  have hqcc : q.IsCocontinuous J K := hq₂
  have e : restrictSheafificationComparisonApp B E h S hS p hp x M =
      (Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso J K q
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))
        (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B)).hom M).hom :=
    Adjunction.homEquiv_counit _ _ _ _
  rw [e]
  exact Iso.isIso_hom _

/-- The comparison between sheafifying and then restricting to the small étale site of the
scheme below `x`, and restricting and then sheafifying: the transpose, across the sheafification
adjunction of the small étale site, of the restriction of the sheafification unit. -/
noncomputable def restrictSheafificationComparison (x : 𝒳) :
    restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) x ⋙ smallEtaleSheafification B E h S hS p x ⟶
      etaleSheafification B S hS p hp ⋙
        restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x where
  app M := restrictSheafificationComparisonApp B E h S hS p hp x M
  naturality {M N} f := by
    let G := restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x
    let adjU := smallEtaleSheafificationAdjunction B E h S hS p x
    let R := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x
    let L := etaleSheafification B S hS p hp
    let η := etaleSheafificationUnit B S hS p hp
    have h₁ := (adjU.homEquiv_naturality_left_symm (Y := R.obj (L.obj N)) (G.map f)
      (G.map (η N))).symm
    have h₂ := (adjU.homEquiv_naturality_right_symm (Y := R.obj (L.obj M))
      (Y' := R.obj (L.obj N)) (G.map (η M)) (R.map (L.map f)))
    have h₃ : G.map f ≫ (G.map (η N) : G.obj N ⟶ (SheafOfModules.forget _).obj (R.obj (L.obj N))) =
        (G.map (η M) : G.obj M ⟶ (SheafOfModules.forget _).obj (R.obj (L.obj M))) ≫
          (SheafOfModules.forget _).map (R.map (L.map f)) :=
      (G.map_comp f (η N)).symm.trans
        ((congrArg G.map (etaleSheafificationUnit_naturality B S hS p hp f)).trans
          (G.map_comp _ _))
    exact h₁.trans ((congrArg (adjU.homEquiv _ _).symm h₃).trans h₂)

/-- The comparison `restrictSheafificationComparison` is an isomorphism. -/
instance isIso_restrictSheafificationComparison (x : 𝒳) :
    IsIso (restrictSheafificationComparison B E h S hS p hp x) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (restrictSheafificationComparison B E h S hS p hp x)
    (isIso_restrictSheafificationComparisonApp B E h S hS p hp x)

end Colimits

/-- **The restriction of étale sheaves of modules to a small étale site preserves colimits.**
Sheafifying and then restricting is restricting and then sheafifying, by
`AlgebraicGeometry.Stack.restrictSheafificationComparison`, and restriction of presheaves of
modules and sheafification both preserve colimits; a diagram of sheaves is the sheafification of
its underlying diagram of presheaves. -/
instance preservesColimitsOfShape_restrictSheafToSmallEtale (x : 𝒳) (K : Type j)
    [Category.{jv} K] [HasColimitsOfShape K AddCommGrpCat.{u}] :
    PreservesColimitsOfShape K (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x) := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  have : PreservesColimitsOfShape K
      (etaleSheafification B S hS p hp ⋙
        restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x) :=
    preservesColimitsOfShape_of_natIso
      (asIso (restrictSheafificationComparison B E h S hS p hp x))
  exact (etaleSheafificationAdjunction B S hS p hp).preservesColimitsOfShape_of_comp_reflector
    _ K

/-- The restriction of étale sheaves of modules to a small étale site is right exact. -/
instance preservesFiniteColimits_restrictSheafToSmallEtale (x : 𝒳) :
    PreservesFiniteColimits (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x) :=
  ⟨fun _ _ _ => inferInstance⟩


/-! ### Closure properties of local quasi-coherence -/

/-- Local quasi-coherence (Stacks 06WJ), as a property of étale sheaves of modules on `𝒳`. -/
abbrev isLocallyQuasicoherent :
    ObjectProperty (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :=
  fun F => IsLocallyQuasicoherent B E h S hS p hp F.val

/-- Local quasi-coherence is invariant under isomorphism of étale sheaves of modules. -/
instance isClosedUnderIsomorphisms_isLocallyQuasicoherent :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderIsomorphisms where
  of_iso {F G} e hF := (isLocallyQuasicoherent_iff B E h S hS p hp G).2 fun x =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((restrictSheafToSmallEtale B E h S hS p hp x).mapIso e)
      ((isLocallyQuasicoherent_iff B E h S hS p hp F).1 hF x)

/-- **Local quasi-coherence is closed under colimits** of every shape along which abelian groups,
modules over a ring and modules on a scheme have colimits: the restriction to the small étale
site of the scheme below an object preserves colimits, and quasi-coherent modules on a small
étale site are closed under them (Descent, Lemma 0GNB). -/
instance isClosedUnderColimitsOfShape_isLocallyQuasicoherent (K : Type j) [Category.{jv} K]
    [HasColimitsOfShape K AddCommGrpCat.{u}]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [∀ U : Scheme.{u}, HasColimitsOfShape K (SheafOfModules.{u} U.ringCatSheaf)] :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderColimitsOfShape K where
  colimitsOfShape_le := by
    rintro F ⟨c⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp F).2 fun x => ?_
    have := SmallEtale.isClosedUnderColimitsOfShape_isQuasicoherentOnSite E (p.obj x).left.1
      (contains_base B E h S hS p x) K
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (restrictSheafToSmallEtale B E h S hS p hp x) c.isColimit)
      fun k => (isLocallyQuasicoherent_iff B E h S hS p hp _).1 (c.prop_diag_obj k) x

/-- **Local quasi-coherence is closed under kernels**: the restriction to a small étale site
preserves kernels, and quasi-coherent modules on a small étale site are closed under kernels. -/
instance isClosedUnderKernels_isLocallyQuasicoherent :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
    let r := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isLimit_kernelFork
      ((KernelFork.isLimitMapConeEquiv k r) (isLimitOfPreserves r hk))
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hF x)
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hG x)

/-- **Local quasi-coherence is closed under cokernels**: the restriction to a small étale site
preserves cokernels, and quasi-coherent modules on a small étale site are closed under
cokernels. -/
instance isClosedUnderCokernels_isLocallyQuasicoherent :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
    let r := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isColimit_cokernelCofork
      ((CokernelCofork.isColimitMapCoconeEquiv k r) (isColimitOfPreserves r hk))
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hF x)
      ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 hG x)

/-- **Local quasi-coherence is closed under finite products**: the restriction to a small étale
site preserves them, and quasi-coherence on a site is closed under finite products. -/
instance isClosedUnderFiniteProducts_isLocallyQuasicoherent :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro F ⟨c⟩
    refine (isLocallyQuasicoherent_iff B E h S hS p hp F).2 fun x => ?_
    exact ObjectProperty.prop_of_isLimit _
      (isLimitOfPreserves (restrictSheafToSmallEtale B E h S hS p hp x) c.isLimit)
      fun k => (isLocallyQuasicoherent_iff B E h S hS p hp _).1 (c.prop_diag_obj k) x⟩


end AlgebraicGeometry.Stack

end
