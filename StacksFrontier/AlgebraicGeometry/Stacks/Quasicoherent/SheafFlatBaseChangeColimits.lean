module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction

/-!
# Colimits in `LQCoh^fbc(𝒪_𝒳)` (Stacks 0771, part (5))

**Stacks 0771** part (5) says that the category `LQCoh^fbc(𝒪_𝒳)` of locally quasi-coherent
modules with the flat base change property on an algebraic stack has colimits, and that they
agree with the colimits in `Mod(𝒳_étale, 𝒪_𝒳)` and in `Mod(𝒪_𝒳)`.

The source proves the étale half from **Stacks 06WM** (local quasi-coherence is closed under
colimits) and **Stacks 0764** (so is the flat base change property).  For the flat base change
property of **Stacks 0762**, read with the inverse image of sheaves, the argument is the one of
**Stacks 0764**: along an arrow `φ` lying over a flat morphism, the sheafified comparison map
`c_φ` is the component of a natural transformation between two functors on `Mod(𝒳_étale, 𝒪_𝒳)`
which preserve colimits.  The first is restriction to the small étale site of the target of `φ`
followed by the inverse image of sheaves of modules, a left adjoint; the second is restriction
to the small étale site of the source of `φ`.  A natural transformation of colimit-preserving
functors which is invertible on a diagram is invertible on its colimit.

## Main results

* `AlgebraicGeometry.Stack.isIso_sheafComparison_app_iff`: for an étale sheaf of modules,
  **Stacks 0762** along an arrow says that the sheafified comparison map is invertible.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isColimit`: **Stacks 0762** is
  closed under colimits of étale sheaves of modules (**Stacks 0764** part (4)).
* `AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_lqcohSheafFbcEtaleModules` and
  `AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_lqcohSheafFbcFppfModules`: `LQCoh^fbc`
  is closed under small colimits in `Mod(𝒳_étale, 𝒪_𝒳)` and in `Mod(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.isColimitMapCoconeFppfToEtaleModules`: those colimits in `Mod(𝒪_𝒳)`
  restrict to colimits in `Mod(𝒳_étale, 𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.lqcohSheafFbc_hasColimits_and_agree`: **Stacks 0771** part (5).

The fppf half uses **Stacks 0771** part (1), that a member of `LQCoh^fbc(𝒪_𝒳)` is an fppf sheaf
(`AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc`), as the source does.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w j

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

section Comparison

variable {x y : 𝒳} (φ : x ⟶ y)

/-- **The sheafified comparison map of Stacks 06WC, as a natural transformation** of functors on
the étale sheaves of `𝒪_𝒳`-modules: restriction to the small étale site of `y` followed by the
inverse image of sheaves of modules, to the sheafification of the restriction to the small
étale site of `x`.  Its component at `F` is the sheafification of the comparison map
`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE` at `F`. -/
def sheafComparison :
    restrictSheafToSmallEtale.{u, u + 1, u, u} B E h S hS p hp y ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ ⟶
      restrictSheafToSmallEtale.{u, u + 1, u, u} B E h S hS p hp x ⋙
        SheafOfModules.forget _ ⋙ smallEtaleSheafification B E h S hS p x where
  app F := (smallEtaleSheafification B E h S hS p x).map
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F.val)
  naturality _ _ f :=
    ((smallEtaleSheafification B E h S hS p x).map_comp _ _).symm.trans
      ((congrArg (smallEtaleSheafification B E h S hS p x).map
        (restrictModulePullbackComparisonUnivLE_naturality B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ f.val)).trans
        ((smallEtaleSheafification B E h S hS p x).map_comp _ _))

/-- For an étale sheaf of modules `F`, the component of
`AlgebraicGeometry.Stack.sheafComparison` at `F` is invertible exactly when the comparison map is
a local isomorphism of the small étale site, which is the condition of **Stacks 0762** along
`φ`. -/
theorem isIso_sheafComparison_app_iff
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsIso ((sheafComparison B E h S hS p hp φ).app F) ↔
      Presheaf.IsLocallyInjective
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B) F.val)) ∧
        Presheaf.IsLocallySurjective
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B) F.val)) := by
  have : (SmallEtale.topology E (p.obj x).left.1
      (contains_base B E h S hS p x)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  rw [← GrothendieckTopology.W_iff_isLocallyBijective, GrothendieckTopology.W_iff,
    ← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rfl

end Comparison

section Colimits

variable (K : Type j) [Category.{j} K] [HasColimitsOfShape K AddCommGrpCat.{u}]

/-- Restriction to the small étale site of `y` followed by the inverse image of sheaves of
modules preserves colimits: the first preserves colimits, the second is a left adjoint. -/
instance preservesColimitsOfShape_restrictSheafToSmallEtale_comp_sheafifiedPullbackComparison
    {x y : 𝒳} (φ : x ⟶ y) :
    PreservesColimitsOfShape K
      (restrictSheafToSmallEtale.{u, u + 1, u, u} B E h S hS p hp y ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ) := by
  have := (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ).leftAdjoint_preservesColimits
  infer_instance

/-- Restriction to the small étale site of `x` followed by forgetting the sheaf condition and
sheafifying preserves colimits: it is isomorphic to the restriction itself. -/
instance preservesColimitsOfShape_restrictSheafToSmallEtale_comp_sheafification (x : 𝒳) :
    PreservesColimitsOfShape K
      (restrictSheafToSmallEtale.{u, u + 1, u, u} B E h S hS p hp x ⋙
        SheafOfModules.forget _ ⋙ smallEtaleSheafification B E h S hS p x) :=
  preservesColimitsOfShape_of_natIso (Functor.isoWhiskerLeft _
    (asIso (smallEtaleSheafificationAdjunction B E h S hS p x).counit) ≪≫
      Functor.rightUnitor _).symm

/-- **Stacks 0762 is closed under colimits** of étale sheaves of modules: the vertex of a colimit
cocone on a diagram of étale sheaves of `𝒪_𝒳`-modules with the flat base change property has the
flat base change property.  Along an arrow over a flat morphism, the sheafified comparison map is
a natural transformation of colimit-preserving functors, invertible on the diagram. -/
theorem hasSheafFlatBaseChangeProperty_of_isColimit
    {D : K ⥤ SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ k, HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (D.obj k).val) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) c.pt.val := by
  intro x y φ hφ
  have : HasColimit D := ⟨c, hc⟩
  have key : IsIso ((sheafComparison B E h S hS p hp φ).app (colimit D)) :=
    NatTrans.isIso_app_colimit _ D fun k =>
      (isIso_sheafComparison_app_iff B E h S hS p hp φ (D.obj k)).2 (hD k φ hφ)
  exact (isIso_sheafComparison_app_iff B E h S hS p hp φ c.pt).1
    ((NatTrans.isIso_app_iff_of_iso _
      (hc.coconePointUniqueUpToIso (colimit.isColimit D))).2 key)

end Colimits

section Stack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The étale half of Stacks 0771, part (5).**  `LQCoh^fbc(𝒪_𝒳)` is closed under colimits in
`Mod(𝒳_étale, 𝒪_𝒳)` of every small shape; so it has colimits and they agree with the colimits of
`Mod(𝒳_étale, 𝒪_𝒳)`.  Local quasi-coherence is closed under colimits by **Stacks 06WM** part (1),
and the flat base change property of **Stacks 0762** by
`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isColimit`, the argument of
**Stacks 0764** part (4). -/
instance isClosedUnderColimitsOfShape_lqcohSheafFbcEtaleModules
    (K : Type u) [Category.{u} K] :
    (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderColimitsOfShape K where
  colimitsOfShape_le := by
    rintro F ⟨c⟩
    have hlqc : (isLocallyQuasicoherent.{u, u + 1, u, u} B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) F :=
      ObjectProperty.prop_of_isColimit _ c.isColimit fun k => (c.prop_diag_obj k).1
    exact ⟨hlqc, hasSheafFlatBaseChangeProperty_of_isColimit B E h S hS _ _ K c.isColimit
      fun k => (c.prop_diag_obj k).2⟩

/-- Restriction of fppf modules to the associated étale site is fully faithful: it changes
neither the presheaves of modules nor the maps between them. -/
def fullyFaithfulFppfToEtaleModules : (fppfToEtaleModules B S hS 𝒳).FullyFaithful where
  preimage f := ⟨f.val⟩

/-- Restriction of fppf modules to the associated étale site is full. -/
instance : (fppfToEtaleModules B S hS 𝒳).Full := (fullyFaithfulFppfToEtaleModules B S hS 𝒳).full

/-- Restriction of fppf modules to the associated étale site is faithful. -/
instance : (fppfToEtaleModules B S hS 𝒳).Faithful :=
  (fullyFaithfulFppfToEtaleModules B S hS 𝒳).faithful

/-- **Colimits of `LQCoh^fbc(𝒪_𝒳)` in `Mod(𝒪_𝒳)` are colimits in `Mod(𝒳_étale, 𝒪_𝒳)`.**  For a
diagram of fppf modules in `LQCoh^fbc(𝒪_𝒳)`, the colimit in the étale sheaves of modules lies in
`LQCoh^fbc(𝒪_𝒳)` by the étale half of **Stacks 0771** part (5), hence is an fppf sheaf by
**Stacks 0771** part (1); being an fppf sheaf, it is the colimit of the diagram in `Mod(𝒪_𝒳)` as
well.  So every colimit cocone in `Mod(𝒪_𝒳)` restricts to a colimit cocone of étale sheaves. -/
def isColimitMapCoconeFppfToEtaleModules {K : Type u} [Category.{u} K]
    {D : K ⥤ fppfModules B S hS 𝒳}
    (hD : ∀ k, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 (D.obj k))
    {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((fppfToEtaleModules B S hS 𝒳).mapCocone c) := by
  have := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  let R := fppfToEtaleModules B S hS 𝒳
  haveI hK : HasColimitsOfShape K (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :=
    inferInstance
  haveI : HasColimit (D ⋙ R) := hK.has_colimit (D ⋙ R)
  let Gc := colimit (D ⋙ R)
  have hG : lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳 Gc :=
    (isClosedUnderColimitsOfShape_lqcohSheafFbcEtaleModules B E h S hS 𝒳 K).colimitsOfShape_le
      Gc ⟨.colimit (D ⋙ R) hD⟩
  let G := fppfModuleOfLqcohSheafFbc B E h S hS 𝒳 Gc hG
  let c' : Cocone D :=
    { pt := G.obj
      ι := { app k := (fullyFaithfulFppfToEtaleModules B S hS 𝒳).preimage
                (colimit.ι (D ⋙ R) k)
             naturality _ _ f := SheafOfModules.hom_ext
                ((congrArg SheafOfModules.Hom.val (colimit.w (D ⋙ R) f)).trans
                  (Category.comp_id _).symm) } }
  have hc' : IsColimit (R.mapCocone c') := colimit.isColimit (D ⋙ R)
  exact hc'.ofIsoColimit ((Cocone.functoriality D R).mapIso
    (hc.uniqueUpToIso (isColimitOfReflects R hc'))).symm

/-- **The fppf half of Stacks 0771, part (5).**  `LQCoh^fbc(𝒪_𝒳)` is closed under small colimits in
`Mod(𝒪_𝒳)`; so it has colimits and they agree with the colimits of `Mod(𝒪_𝒳)`.  By
`AlgebraicGeometry.Stack.isColimitMapCoconeFppfToEtaleModules` they also agree with the colimits
of `Mod(𝒳_étale, 𝒪_𝒳)`. -/
instance isClosedUnderColimitsOfShape_lqcohSheafFbcFppfModules
    (K : Type u) [Category.{u} K] :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).IsClosedUnderColimitsOfShape K where
  colimitsOfShape_le := by
    rintro F ⟨c⟩
    have := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
    have hc := isColimitMapCoconeFppfToEtaleModules B E h S hS 𝒳 c.prop_diag_obj c.isColimit
    exact (isClosedUnderColimitsOfShape_lqcohSheafFbcEtaleModules B E h S hS 𝒳 K).colimitsOfShape_le
      _ ⟨⟨⟨_, _, hc⟩, c.prop_diag_obj⟩⟩

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- **Stacks 0771, part (5).**  The category `LQCoh^fbc(𝒪_𝒳)` has colimits, and they agree with
colimits in `Mod(𝒳_étale, 𝒪_𝒳)` as well as in `Mod(𝒪_𝒳)`.

In order: `LQCoh^fbc(𝒪_𝒳)`, read inside `Mod(𝒪_𝒳)`, has small colimits and its inclusion
preserves them; read inside `Mod(𝒳_étale, 𝒪_𝒳)` the same holds; and restricting a colimit
cocone in `Mod(𝒪_𝒳)` of objects of `LQCoh^fbc(𝒪_𝒳)` to the étale site gives a colimit cocone in
`Mod(𝒳_étale, 𝒪_𝒳)`, so the two readings compute the same colimits. -/
@[stacks 0771 "part (5): LQCoh^fbc(𝒪_𝒳) has small colimits, agreeing with those of Mod(𝒪_𝒳) \
  and of Mod(𝒳_étale, 𝒪_𝒳)"]
theorem lqcohSheafFbc_hasColimits_and_agree :
    HasColimitsOfSize.{u, u} (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ∧
      PreservesColimitsOfSize.{u, u} (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ∧
      (HasColimitsOfSize.{u, u}
          (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ∧
        PreservesColimitsOfSize.{u, u} (lqcohSheafFbcEtaleModules.{u, w, u} B E h S hS 𝒳).ι) ∧
      ∀ {K : Type u} [Category.{u} K] {D : K ⥤ fppfModules B S hS 𝒳},
        (∀ k, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 (D.obj k)) →
          ∀ {c : Cocone D}, IsColimit c →
            Nonempty (IsColimit ((fppfToEtaleModules B S hS 𝒳).mapCocone c)) := by
  have := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  exact ⟨⟨fun K => inferInstance⟩, ⟨inferInstance⟩, ⟨⟨fun K => inferInstance⟩, ⟨inferInstance⟩⟩,
    fun hD _ hc => ⟨isColimitMapCoconeFppfToEtaleModules B E h S hS 𝒳 hD hc⟩⟩

end Stack

end AlgebraicGeometry.Stack
