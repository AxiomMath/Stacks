module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksFrontier.CategoryTheory.Sites.FullSubcategorySite

/-!
# The small smooth, syntomic and fppf sites of a scheme

Let `S` be a scheme of a chosen big fppf site `B`, and let `τ ∈ {smooth, syntomic, fppf}`.
**The small `τ`-site `S_τ` of `S`** is the full subcategory of the big `τ`-site `(Sch/S)_τ` on
the schemes `T → S` whose structure morphism is smooth, syntomic, respectively flat and locally of
finite presentation, and a family of morphisms of `S_τ` covers when its image covers in
`(Sch/S)_τ`. This is the construction of the small étale site in Topologies, Definition 021C with
the étale morphisms replaced by the morphisms of the topology.

The objects of `S_τ` are closed under the members of `τ`-coverings, so the inclusion
`S_τ ⊆ (Sch/S)_τ` is continuous and cocontinuous.

## Main definitions

* `AlgebraicGeometry.FlatSiteKind`: the three topologies `τ ∈ {smooth, syntomic, fppf}`, with
  `AlgebraicGeometry.FlatSiteKind.toSiteKind` the topology and
  `AlgebraicGeometry.FlatSiteKind.morphismProperty` the class of morphisms of its coverings.
* `AlgebraicGeometry.SmallFlatSite`: the small `τ`-site `S_τ` of `S`, with its inclusion
  `AlgebraicGeometry.SmallFlatSite.inclusion` into `(Sch/S)_τ` and its topology
  `AlgebraicGeometry.SmallFlatSite.topology`.
* `AlgebraicGeometry.SmallFlatSite.opensToSmall`: the small Zariski site of `S` inside `S_τ`.
* `AlgebraicGeometry.SmallFlatSite.structureSheaf`: the structure sheaf `T ↦ Γ(T, 𝒪_T)` of `S_τ`,
  the restriction of that of `(Sch/S)_τ`, and `AlgebraicGeometry.SmallFlatSite.ringedSite` the
  ringed site `(S_τ, 𝒪)`.

## Main results

* `AlgebraicGeometry.SmallFlatSite.isContinuous_inclusion` and
  `AlgebraicGeometry.SmallFlatSite.isCocontinuous_inclusion`: the inclusion into the big site is
  continuous and cocontinuous.
* `AlgebraicGeometry.SmallFlatSite.isTerminalFinal` and
  `AlgebraicGeometry.SmallFlatSite.isTerminalInclusionFinal`: `S → S` is a final object of `S_τ`,
  and the inclusion carries it to a final object of `(Sch/S)_τ`.

## References

* [Stacks Project, Tag 021C](https://stacks.math.columbia.edu/tag/021C)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The three topologies `τ ∈ {smooth, syntomic, fppf}` on schemes. -/
inductive FlatSiteKind where
  /-- The smooth topology. -/
  | smooth
  /-- The syntomic topology. -/
  | syntomic
  /-- The fppf topology. -/
  | fppf

namespace FlatSiteKind

/-- The topology of the indicated kind, as one of the five topologies of the big sites. -/
def toSiteKind : FlatSiteKind → SiteKind
  | smooth => .smooth
  | syntomic => .syntomic
  | fppf => .fppf

/-- The class of morphisms of schemes of which the coverings of the indicated topology consist:
smooth, syntomic, respectively flat and locally of finite presentation morphisms. -/
def morphismProperty : FlatSiteKind → MorphismProperty Scheme.{u}
  | smooth => @Smooth
  | syntomic => @Syntomic
  | fppf => @Flat ⊓ @LocallyOfFinitePresentation

/-- Each of the three classes of morphisms is stable under base change. -/
instance (κ : FlatSiteKind) : (morphismProperty.{u} κ).IsStableUnderBaseChange := by
  cases κ
  · exact inferInstanceAs (MorphismProperty.IsStableUnderBaseChange @Smooth)
  · exact syntomic_isStableUnderBaseChange
  · exact (Stack.flat_and_locallyOfFinitePresentation_instances.{u}).2.2

/-- Each of the three classes of morphisms is stable under composition. -/
instance (κ : FlatSiteKind) : (morphismProperty.{u} κ).IsStableUnderComposition := by
  cases κ
  · exact inferInstanceAs (MorphismProperty.IsStableUnderComposition @Smooth)
  · exact syntomic_isStableUnderComposition
  · exact (Stack.flat_and_locallyOfFinitePresentation_instances.{u}).2.1

/-- Each of the three classes of morphisms contains the identities. -/
instance (κ : FlatSiteKind) : (morphismProperty.{u} κ).ContainsIdentities := by
  cases κ
  · exact inferInstanceAs (MorphismProperty.ContainsIdentities @Smooth)
  · exact ⟨fun X ↦ syntomic_of_isOpenImmersion (𝟙 X)⟩
  · exact (Stack.flat_and_locallyOfFinitePresentation_instances.{u}).1

/-- An open immersion is a morphism of each of the three classes. -/
theorem morphismProperty_of_isOpenImmersion (κ : FlatSiteKind) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : morphismProperty κ f := by
  cases κ
  · exact (inferInstance : Smooth f)
  · exact syntomic_of_isOpenImmersion f
  · exact ⟨inferInstance, inferInstance⟩

/-- A morphism of each of the three classes is flat. -/
theorem flat_of_morphismProperty (κ : FlatSiteKind) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : morphismProperty κ f) : Flat f := by
  cases κ
  · have : Smooth f := hf
    infer_instance
  · exact AlgebraicGeometry.flat hf
  · exact hf.1

/-- A morphism of each of the three classes is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_morphismProperty (κ : FlatSiteKind) {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : morphismProperty κ f) : LocallyOfFinitePresentation f := by
  cases κ
  · have : Smooth f := hf
    infer_instance
  · exact AlgebraicGeometry.locallyOfFinitePresentation hf
  · exact hf.2

variable (B : BigFppfSite.{u})

/-- The chosen covering families of the indicated topology on the common category of schemes of
a big fppf site, as a precoverage: they generate `B.baseTopology κ.toSiteKind`. -/
def basePrecoverage : FlatSiteKind → Precoverage B.Schemes
  | smooth => B.smoothPrecoverage
  | syntomic => B.syntomicPrecoverage
  | fppf => B.precoverage

/-- The topology of the indicated kind on the schemes of `B` is generated by its chosen covering
families. -/
theorem baseTopology_toSiteKind (κ : FlatSiteKind) :
    B.baseTopology κ.toSiteKind = (basePrecoverage B κ).toGrothendieck := by
  cases κ <;> rfl

/-- **The members of a chosen covering family of the indicated topology are morphisms of its
class.** -/
theorem morphismProperty_of_mem_basePrecoverage (κ : FlatSiteKind) ⦃V : B.Schemes⦄
    (R : Presieve V) (hR : R ∈ basePrecoverage B κ V) ⦃W : B.Schemes⦄ (g : W ⟶ V)
    (hg : R g) : morphismProperty κ (B.inclusion.map g) := by
  cases κ
  · obtain ⟨E, rfl, -, hE⟩ := hR
    obtain ⟨i⟩ := hg
    have hE' : (E.map B.inclusion).presieve₀ ∈ Scheme.precoverage @Smooth _ := hE
    exact ((Scheme.presieve₀_mem_precoverage_iff _).1 hE').2 i
  · obtain ⟨E, rfl, -, hE⟩ := hR
    obtain ⟨i⟩ := hg
    exact hE.1 i
  · exact Stack.flat_and_locallyOfFinitePresentation_of_mem_precoverage B R hR g hg

end FlatSiteKind

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- The objects of the big fppf category over `S` whose structure morphism belongs to the class
of the indicated topology. -/
def IsSmallFlatSiteObj : ObjectProperty (BigFppfOver B S hS) :=
  fun X ↦ κ.morphismProperty X.hom.hom

/-- The morphisms of the big fppf category over `S` whose underlying morphism of schemes belongs
to the class of the indicated topology. -/
abbrev smallFlatSiteMorphisms : MorphismProperty (BigFppfOver B S hS) :=
  (κ.morphismProperty.inverseImage B.inclusion).inverseImage (forget B S hS)

/-- If `f : X ⟶ Y` is a morphism of the class and `Y` is an object of the small site, then so is
`X`. -/
theorem isSmallFlatSiteObj_of_smallFlatSiteMorphisms ⦃X Y : BigFppfOver B S hS⦄ (f : X ⟶ Y)
    (hf : smallFlatSiteMorphisms B S hS κ f) (hY : IsSmallFlatSiteObj B S hS κ Y) :
    IsSmallFlatSiteObj B S hS κ X := by
  have h : X.hom.hom = f.left.hom ≫ Y.hom.hom := by rw [← Over.w f]; rfl
  rw [IsSmallFlatSiteObj, h]
  exact κ.morphismProperty.comp_mem _ _ hf hY

/-- Every covering sieve of the big `τ`-site of `S` is refined by a covering family of morphisms
of the class of `τ`. -/
theorem isRefinableBy_smallFlatSiteMorphisms ⦃X : BigFppfOver B S hS⦄ (T : Sieve X)
    (hT : T ∈ baseOverTopology B S hS κ.toSiteKind X) :
    (baseOverTopology B S hS κ.toSiteKind).IsRefinableBy (smallFlatSiteMorphisms B S hS κ) T := by
  refine GrothendieckTopology.isRefinableBy_over (B.baseTopology κ.toSiteKind)
    (κ.morphismProperty.inverseImage B.inclusion) (B.obj hS) (fun Y T' hT' ↦ ?_) T hT
  rw [FlatSiteKind.baseTopology_toSiteKind] at hT' ⊢
  exact Stack.isRefinableBy_toGrothendieck_of_members B κ.morphismProperty
    (FlatSiteKind.basePrecoverage B κ) (FlatSiteKind.morphismProperty_of_mem_basePrecoverage B κ)
    T' hT'

end BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- **The small `τ`-site of `S`, for `τ ∈ {smooth, syntomic, fppf}`.**  The full subcategory of
the big `τ`-site `(Sch/S)_τ` on the schemes `T → S` whose structure morphism is smooth, syntomic,
respectively flat and locally of finite presentation. -/
abbrev SmallFlatSite := (BigFppfOver.IsSmallFlatSiteObj B S hS κ).FullSubcategory

namespace SmallFlatSite

/-- The inclusion of the small `τ`-site of `S` into the big `τ`-site. -/
abbrev inclusion : SmallFlatSite B S hS κ ⥤ BigFppfOver B S hS :=
  (BigFppfOver.IsSmallFlatSiteObj B S hS κ).ι

/-- **The topology of the small `τ`-site of `S`**: a family of morphisms covers when its image
covers in the big `τ`-site `(Sch/S)_τ`.  This is the topology the full subcategory inherits
(Stacks 06NV). -/
abbrev topology : GrothendieckTopology (SmallFlatSite B S hS κ) :=
  (inclusion B S hS κ).inheritedTopology (BigFppfOver.baseOverTopology B S hS κ.toSiteKind)

/-- **The inclusion of the small `τ`-site into the big `τ`-site is continuous** (Stacks 07AK). -/
instance isContinuous_inclusion :
    (inclusion B S hS κ).IsContinuous (topology B S hS κ)
      (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) :=
  ObjectProperty.isContinuous_ι_inheritedTopology
    (Q := BigFppfOver.smallFlatSiteMorphisms B S hS κ) (fun _ _ _ _ _ _ ↦ inferInstance)
    (BigFppfOver.isSmallFlatSiteObj_of_smallFlatSiteMorphisms B S hS κ)
    (BigFppfOver.isRefinableBy_smallFlatSiteMorphisms B S hS κ)

/-- **The inclusion of the small `τ`-site into the big `τ`-site is cocontinuous** (Stacks 07AK):
a covering of an object of the small site is refined by a covering family whose members lie in
the small site. -/
instance isCocontinuous_inclusion :
    (inclusion B S hS κ).IsCocontinuous (topology B S hS κ)
      (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) :=
  ObjectProperty.isCocontinuous_ι_inheritedTopology
    (BigFppfOver.isSmallFlatSiteObj_of_smallFlatSiteMorphisms B S hS κ)
    (BigFppfOver.isRefinableBy_smallFlatSiteMorphisms B S hS κ)

/-- An open of `S` is an object of the small `τ`-site, through its open immersion. -/
theorem isSmallFlatSiteObj_opensObj (U : S.Opens) :
    BigFppfOver.IsSmallFlatSiteObj B S hS κ (BigFppfOver.opensObj B S hS U) :=
  κ.morphismProperty_of_isOpenImmersion U.ι

/-- **The small Zariski site of `S` inside the small `τ`-site of `S`.** -/
noncomputable def opensToSmall : S.Opens ⥤ SmallFlatSite B S hS κ :=
  ObjectProperty.lift _ (BigFppfOver.opensToBig B S hS) (isSmallFlatSiteObj_opensObj B S hS κ)

/-- Including the opens of `S` into the small `τ`-site and then into the big site is including
them into the big site. -/
theorem opensToSmall_comp_inclusion :
    opensToSmall B S hS κ ⋙ inclusion B S hS κ = BigFppfOver.opensToBig B S hS :=
  rfl

/-- The final object `S → S` of the small `τ`-site. -/
noncomputable def final : SmallFlatSite B S hS κ := (opensToSmall B S hS κ).obj ⊤

/-- `S → S` is a final object of the small `τ`-site. -/
noncomputable def isTerminalFinal : IsTerminal (final B S hS κ) :=
  IsTerminal.ofUniqueHom (fun Y ↦ ObjectProperty.homMk
      ((BigFppfOver.isTerminalOpensObjTop B S hS).from Y.obj))
    (fun _ _ ↦ ObjectProperty.hom_ext _ ((BigFppfOver.isTerminalOpensObjTop B S hS).hom_ext _ _))

/-- The inclusion carries the final object of the small `τ`-site to a final object of the big
site. -/
noncomputable def isTerminalInclusionFinal :
    IsTerminal ((inclusion B S hS κ).obj (final B S hS κ)) :=
  BigFppfOver.isTerminalOpensObjTop B S hS

/-- The small `τ`-site of `S` is essentially small. -/
instance essentiallySmall : EssentiallySmall.{u} (SmallFlatSite B S hS κ) :=
  essentiallySmall_of_fully_faithful (inclusion B S hS κ)

/-- Abelian presheaves on the small `τ`-site of `S` have a sheafification. -/
instance hasSheafify_topology : HasSheafify (topology B S hS κ) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on the small `τ`-site are the locally bijective
maps. -/
instance wEqualsLocallyBijective_topology :
    (topology B S hS κ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Abelian presheaves on every localization of the small `τ`-site have a sheafification. -/
instance hasSheafify_over (X : SmallFlatSite B S hS κ) :
    HasSheafify ((topology B S hS κ).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on every localization of the small `τ`-site are the
locally bijective maps. -/
instance wEqualsLocallyBijective_over (X : SmallFlatSite B S hS κ) :
    ((topology B S hS κ).over X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **The structure sheaf of the small `τ`-site of `S`**, `T ↦ Γ(T, 𝒪_T)`: the restriction of the
structure sheaf of the big `τ`-site. -/
noncomputable def structureSheaf : Sheaf (topology B S hS κ) CommRingCat.{u} :=
  ((inclusion B S hS κ).sheafPushforwardContinuous CommRingCat.{u} (topology B S hS κ)
    (BigFppfOver.baseOverTopology B S hS κ.toSiteKind)).obj
    (FibredSite.baseStructureSheaf B S hS κ.toSiteKind)

/-- The underlying sheaf of rings of the structure sheaf of the small `τ`-site: the restriction
of that of the big `τ`-site. -/
noncomputable abbrev ringStructureSheaf : Sheaf (topology B S hS κ) RingCat.{u} :=
  ((inclusion B S hS κ).sheafPushforwardContinuous RingCat.{u} (topology B S hS κ)
    (BigFppfOver.baseOverTopology B S hS κ.toSiteKind)).obj
    (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind)

/-- The sections of the structure sheaf of the small `τ`-site over `T` are the global functions
on `T`. -/
@[simp] theorem structureSheaf_obj :
    (structureSheaf B S hS κ).obj =
      (inclusion B S hS κ).op ⋙ (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ :=
  rfl

/-- The small `τ`-site of `S` with its structure sheaf, as a ringed site. -/
noncomputable abbrev ringedSite : RingedSite.{u + 1, u, u} where
  C := SmallFlatSite B S hS κ
  J := topology B S hS κ
  O := structureSheaf B S hS κ

end SmallFlatSite

end AlgebraicGeometry

end
