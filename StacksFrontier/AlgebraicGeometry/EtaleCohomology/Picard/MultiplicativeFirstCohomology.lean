module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePicard
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardShrink
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Cohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first étale cohomology of the multiplicative group is the Picard group

For a scheme `S`, `H¹(S_étale, 𝐆_m) = Pic(S)`: this is the étale identification of
[Stacks, Tag 03P8].

The identification passes through the small étale ringed site of `S`: its first cohomology of the
units is the Picard group of the ringed site by [Stacks, Tag 040E] (the small étale site is locally
ringed, Tag 04HZ), and the Picard group of the small étale ringed site is the Picard group of `S`
because invertible modules on `S_étale` are quasi-coherent and `𝓕 ↦ 𝓕^a` is an equivalence on
quasi-coherent modules ([Stacks, Tag 03DX] (2)),
`AlgebraicGeometry.SmallEtale.picardGroupAssociatedModuleAddEquiv`.

## Main definitions

* `Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard`: **Stacks 03P8, the étale identification**
  `H¹_étale(S, 𝐆_m) ≃+ Pic(S)`, on Mathlib's small étale site, for the `𝐆_m` of the Kummer sequence
  (`Stacks.Kummer.multiplicativeSheaf`) and `Pic(S) = Stacks.Picard.ofScheme S`.
* `AlgebraicGeometry.SmallEtale.h1UnitsAddEquivOfScheme`: `H¹(S_étale, 𝒪^*) ≃+ Pic(S)` on the
  size-bounded small étale site of Stacks 021B.
* `AlgebraicGeometry.SmallEtale.h1MultiplicativeAddEquivOfContains`: the same on Mathlib's site
  with coefficients in `AddCommGrpCat.{u + 1}`, through a size-bounded site containing `S`.
* `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroupSkeleton`: Stacks 040E on an
  essentially small locally ringed site, landing in the Picard group of isomorphism classes.

## Implementation notes

The Zariski identification of [Stacks, Tag 03P8] is
`Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`. The `Ext` universe `w` and the
coefficient universe of `𝐆_m` are arbitrary: `H¹` does not depend on the coefficient universe
(`Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv`).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.Cohomology.Torsors.Generators

universe w v u

namespace Stacks.Cohomology.Torsors.Generators

section General

variable (X : AlgebraicGeometry.RingedSite.{u + 1, u, u}) [EssentiallySmall.{u} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{u + 1} (Sheaf X.J AddCommGrpCat.{u})]
  [HasExt.{u + 1} (Sheaf (AlgebraicGeometry.RingedSite.smallTopology X) AddCommGrpCat.{u})]

/-- `H¹(X, 𝒪_X^*) ≃+ Pic(X)` (Stacks 040E) on an essentially small locally ringed site `X`, with
the Picard group the group of isomorphism classes of invertible modules
(`Stacks.SheafOfModules.PicardGroup`). -/
@[ega "0 5.4.7" "Group isomorphism H^1(X",
  sga "1 XI 6.4" "more general",
  sga "3 VIII 4.4" "H¹(O^×) ≅ Pic"]
def h1UnitsAddEquivPicardGroupSkeleton (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) :
    Sheaf.H.{u + 1} (unitsAddSheaf X) 1 ≃+
      Stacks.SheafOfModules.PicardGroup X.O.obj
        (show Presheaf.IsSheaf X.J
            (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj) from
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) :=
  (h1UnitsAddEquivPicardGroupOfEssentiallySmall X hX).trans
    (Stacks.SheafOfModules.picardGroupShrinkAddEquiv (J := X.J) X.O.obj
      (show Presheaf.IsSheaf X.J
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj) from
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).symm

end General

end Stacks.Cohomology.Torsors.Generators

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian sheaves on the small étale ringed site of `S`, with coefficients at the universe of the
structure rings, form a Grothendieck abelian category: the site is essentially small. -/
instance isGrothendieckAbelian_sheaf_smallEtaleRingedSite :
    IsGrothendieckAbelian.{u} (Sheaf (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u}) :=
  haveI := smallEtaleRingedSite_essentiallySmall B S hS
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _

/-- The `Ext` groups of abelian sheaves on the small étale ringed site of `S` live in the universe
`u + 1` of the objects of the site. -/
instance hasExt_sheaf_smallEtaleRingedSite :
    HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- On the localization of the topology of the small étale ringed site at `V`, the weak
equivalences of abelian sheaves are the locally bijective maps. -/
instance wEqualsLocallyBijective_smallEtaleRingedSite_over (V : SmallEtale B S hS) :
    ((smallEtaleRingedSite B S hS).J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs (((topology B S hS).over V).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- **`H¹(S_étale, 𝒪^*) = Pic(S)`** on the size-bounded small étale site of `S`. -/
def h1UnitsAddEquivOfScheme :
    Sheaf.H.{u + 1} (unitsAddSheaf (smallEtaleRingedSite B S hS)) 1 ≃+
      Stacks.Picard.ofScheme S := by
  haveI := smallEtaleRingedSite_essentiallySmall B S hS
  haveI : HasExt.{u + 1} (Sheaf (AlgebraicGeometry.RingedSite.smallTopology
      (smallEtaleRingedSite B S hS)) AddCommGrpCat.{u}) := HasExt.standard _
  exact (Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroupSkeleton
    (smallEtaleRingedSite B S hS) (smallEtaleRingedSite_isLocallyRinged B S hS)).trans
      (picardGroupAssociatedModuleAddEquiv B S hS).symm

/-- The restriction of `𝐆_m` from Mathlib's small étale site of `S` to the size-bounded one is the
universe lift of the sheaf of units of the small étale ringed site. -/
def multiplicativeSheafRestrictionIso :
    ((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (topology B S hS)
        S.smallEtaleTopology).obj (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S) ≅
      (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} (topology B S hS)).obj
        (unitsAddSheaf (smallEtaleRingedSite B S hS)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- Postcomposition with an isomorphism, as an additive equivalence of `Ext` groups. -/
def extPostcompIsoAddEquiv {D : Type*} [Category D] [Abelian D] [HasExt.{w} D]
    {X Y Y' : D} (e : Y ≅ Y') (n : ℕ) : Abelian.Ext.{w} X Y n ≃+ Abelian.Ext.{w} X Y' n where
  toFun y := y.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)
  invFun z := z.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)
  left_inv y := by
    simp only
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero n) (add_zero 0) (add_zero n),
      Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id, Abelian.Ext.comp_mk₀_id]
  right_inv z := by
    simp only
    rw [Abelian.Ext.comp_assoc _ _ _ (add_zero n) (add_zero 0) (add_zero n),
      Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id, Abelian.Ext.comp_mk₀_id]
  map_add' y₁ y₂ := Abelian.Ext.add_comp _ _ _ _

/-- **`H¹(S_étale, 𝐆_m) = Pic(S)`** on Mathlib's small étale site, with coefficients in
`AddCommGrpCat.{u + 1}`, through a size-bounded small étale site containing `S`. -/
def h1MultiplicativeAddEquivOfContains :
    letI := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
    Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S) 1 ≃+
      Stacks.Picard.ofScheme S := by
  letI := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
  haveI : ∀ T : (S.Etale)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow T (toEtaleSite B S hS).op) AddCommGrpCat.{u + 1} :=
    fun _ => Limits.hasLimitsOfShape_of_essentiallySmall.{u} _ _
  haveI : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  haveI : HasSheafify (topology B S hS) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  haveI : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :=
    smallEtaleSheaf_isGrothendieckAbelian B ⟨S, hS⟩
  haveI : HasExt.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasExt _
  exact (Stacks.Cohomology.DenseSubsite.hAddEquiv (topology B S hS) S.smallEtaleTopology
      (toEtaleSite B S hS) (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S) 1).trans
    ((extPostcompIsoAddEquiv (multiplicativeSheafRestrictionIso B S hS) 1).trans
      ((Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv.{u + 1, u + 1, u + 1, u, u, u + 1}
        (topology B S hS) (unitsAddSheaf (smallEtaleRingedSite B S hS))).symm.trans
        (h1UnitsAddEquivOfScheme B S hS)))

end AlgebraicGeometry.SmallEtale

namespace Stacks.Kummer

open _root_.AlgebraicGeometry

variable (S : Scheme.{u})

/-- `𝐆_m` with coefficients in a larger universe is the universe lift of `𝐆_m` with coefficients in
`AddCommGrpCat.{u + 1}`. -/
noncomputable def multiplicativeSheafUliftIso :
    multiplicativeSheaf.{u, v} S ≅
      (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{max (u + 1) v, u + 1}
        S.smallEtaleTopology).obj (multiplicativeSheaf.{u, u + 1} S) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun _ => (AddEquiv.ulift.trans (AddEquiv.ulift.trans AddEquiv.ulift).symm).toAddCommGrpIso)
      (fun _ => rfl))

/-- **Stacks Project, Tag 03P8, the étale identification.** For any scheme `X`, the first étale
cohomology of the multiplicative group is the Picard group: `H¹_étale(X, 𝐆_m) = Pic(X)`.

The identification is the composite of the canonical ones: restriction to a size-bounded small
étale site (Tag 00XU), the identification of `H¹` of the units of the small étale ringed site with
its Picard group (Tag 040E), and the identification of that Picard group with `Pic(X)` by
`𝓕 ↦ 𝓕^a` (Tag 03DX (2)); the coefficient universe of `𝐆_m` is immaterial for `H¹`. -/
@[stacks 03P8 "the étale identification H¹_étale(X, 𝐆_m) = Pic(X), for every scheme X; the \
fppf, syntomic and smooth identifications are not covered",
  sga "4 IX 3.3",
  sga "4 XII 8.6",
  sga "4½ Arcata 2.2.3",
  sga "4½ Arcata 3.3.1" "more general"]
noncomputable def etaleH1MultiplicativeAddEquivPicard
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} S) 1 ≃+ Stacks.Picard.ofScheme S := by
  letI := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
  have hS : (BigEtaleSite.ofSet {S}).Contains S := BigEtaleSite.contains_ofSet _ (by simp)
  exact (SmallEtale.extPostcompIsoAddEquiv.{w} (multiplicativeSheafUliftIso.{v, u} S) 1).trans
    ((Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv.{u + 1, w, max (u + 1) v, u + 1, u, u + 1}
        S.smallEtaleTopology (multiplicativeSheaf.{u, u + 1} S)).symm.trans
      (SmallEtale.h1MultiplicativeAddEquivOfContains (BigEtaleSite.ofSet {S}) S hS))

end Stacks.Kummer
