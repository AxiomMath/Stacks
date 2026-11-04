module

public import Mathlib.CategoryTheory.Sites.Coverage
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpenEqualityLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiPullbackSections
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsReflection

/-!
# fpqc descent for a sheaf pulled back from the small Zariski site, up to local representability

Let `S` be a scheme in a big Zariski site `B`, let `F` be a sheaf of sets on the small Zariski
site of `S`, and let `π_S⁻¹F` be its inverse image along the projection from the big Zariski
topos over `S`. This file proves the uniqueness half of the fpqc sheaf condition for `π_S⁻¹F`
unconditionally, and the existence half from one remaining geometric input, the *local
representability* of compatible families.

The tool is an equality locus on the big site. Two sections of `π_S⁻¹F` over an object `X` of
the big Zariski site over `S` agree on a largest open subscheme of `X`: there is an open
`W ⊆ X` such that a morphism `h : Y ⟶ X` of schemes over `S` has the same restrictions of the
two sections exactly when the image of `Y` lies in `W`. This is the Zariski half of Stacks 09XM
read on the big site, through the sections formula.

Two consequences carry the proof. First, two sections of `π_S⁻¹F` which agree along a family of
morphisms that is jointly surjective on points are equal — geometric uniqueness, with no
flatness or quasi-compactness needed, and in particular the uniqueness half of the fpqc sheaf
condition. Second, the equality loci of a compatible family on an fpqc covering descend, by
Stacks 03N0, to a single open of the base: this is the first paragraph of the proof of
Stacks 09XN.

Granted local representability — after a refinement generating a big Zariski covering, every
compatible family is given by sections over the members of that covering, agreeing with the
original family on the fibre products — the existence of an amalgamation follows: the local
sections are themselves a compatible family for the refined covering by geometric uniqueness,
they glue because `π_S⁻¹F` is a sheaf for the big Zariski topology, and the glued section
restricts to the original family again by geometric uniqueness.

## Main definitions

* `AlgebraicGeometry.zariskiInverseImagePresheaf` — the presheaf on the big Zariski site over
  `S` underlying `π_S⁻¹F`.
* `AlgebraicGeometry.zariskiInverseImageEqLocus` — the largest open of `X` on which two sections
  of `π_S⁻¹F` over `X` agree.
* `AlgebraicGeometry.BigZariskiOver.pairProduct` — the fibre product of two objects over `X` in
  the big Zariski site over `S`, with its two projections.

## Main results

* `AlgebraicGeometry.forall_mem_zariskiInverseImageEqLocus_iff` — the universal property of the
  equality locus.
* `AlgebraicGeometry.zariskiInverseImageEqLocus_preimage` — the equality locus is compatible
  with restriction.
* `AlgebraicGeometry.eq_of_zariskiInverseImage_map_eq_of_jointlySurjective` — geometric
  uniqueness of sections of `π_S⁻¹F` along a jointly surjective family.
* `AlgebraicGeometry.smallZariskiProjection_inverseImage_isSeparatedFor_fpqc` — the uniqueness
  half of the fpqc sheaf condition for `π_S⁻¹F`.
* `AlgebraicGeometry.existsUnique_preimage_eq_zariskiInverseImageEqLocus` — **Stacks 09XN,
  step 4**: the equality loci of a compatible family on an fpqc covering descend to the base.
* `AlgebraicGeometry.exists_isAmalgamation_of_locallyRepresentable_zariski` and
  `AlgebraicGeometry.smallZariskiProjection_inverseImage_isSheaf_fpqc_of_locallyRepresentable` —
  the existence half, and hence the whole fpqc sheaf condition, from local representability.

## Implementation notes

The sections formula `AlgebraicGeometry.zariskiInverseImageSectionsIso` turns a section of
`π_S⁻¹F` over `X` into a global section of the small-site pullback of `F` to `X`, presented as
a morphism out of a terminal sheaf by `CategoryTheory.Sheaf.ΓEquivHomTerminal`; the equality
locus is the open of Stacks 09XM attached to the resulting pair of global sections. What makes
the universal property an equivalence rather than an implication is
`CategoryTheory.sheafPullbackSectionsRestriction_eq_iff`: restriction along `h` in the presheaf
`π_S⁻¹F` corresponds, under the sections formula, to the sections-restriction map of the
small-site pullbacks, and that map has exactly the same fibres as inverse image along `h`.

Compatibility with restriction is proved by testing both opens against the morphisms out of
their own open subschemes, which are objects of the big Zariski site over `S` because the site
is closed under passing to opens.

Fibre products are taken in the size-bounded category of schemes of `B` and equipped with a
structure morphism by hand rather than formed in the slice category, so that their projections
are literally the projections of the underlying fibre product of schemes; Stacks 03N0 is stated
for the fibre product of schemes, and the two are compared by
`CategoryTheory.Limits.PreservesPullback.iso`.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

section Relative

variable (B : BigZariskiSite.{u}) (S : B.Schemes)
  (F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)))

/-- The presheaf on the big Zariski site over `S` underlying `π_S⁻¹F`. By the sections formula
`AlgebraicGeometry.zariskiInverseImageSectionsIso` it is `X ↦ Γ(X_Zar, f_X⁻¹F)`. -/
public abbrev zariskiInverseImagePresheaf :
    (BigZariskiOver B S.obj S.property)ᵒᵖ ⥤ Type (u + 1) :=
  ((smallZariskiProjection B S).inverseImage.obj F).obj

/-- The pullback of `F` to the small Zariski site of an object `X` of the big Zariski site over
`S`, along the structure morphism of `X`. -/
public abbrev zariskiSmallPullbackSheaf (X : BigZariskiOver B S.obj S.property) :
    Sheaf (SmallZariski.topology B X.left.obj X.left.property) (Type (u + 1)) :=
  (smallZariskiSitePullback B X.hom).obj F

/-- A section of `π_S⁻¹F` over `X`, read through the sections formula as a morphism from the
terminal sheaf on the small Zariski site of `X` to the small-site pullback of `F` to `X`. -/
public def zariskiInverseImageSectionHom (X : BigZariskiOver B S.obj S.property)
    (t : (zariskiInverseImagePresheaf B S F).obj (op X)) :
    (⊤_ (Sheaf (SmallZariski.topology B X.left.obj X.left.property) (Type (u + 1)))) ⟶
      zariskiSmallPullbackSheaf B S F X :=
  Sheaf.ΓEquivHomTerminal (SmallZariski.topology B X.left.obj X.left.property) _
    ((zariskiInverseImageSectionsIso B S X).hom.app F t)

/-- **The equality locus of two sections of `π_S⁻¹F`.** The largest open subscheme of `X` on
which two sections of `π_S⁻¹F` over `X` agree, namely the open of Stacks 09XM attached to the
two corresponding global sections of the small-site pullback of `F` to `X`. -/
public def zariskiInverseImageEqLocus (X : BigZariskiOver B S.obj S.property)
    (t₁ t₂ : (zariskiInverseImagePresheaf B S F).obj (op X)) :
    (B.inclusion.obj X.left).Opens :=
  zariskiOpenEqLocus B X.left (zariskiInverseImageSectionHom B S F X t₁)
    (zariskiInverseImageSectionHom B S F X t₂)

/-- The sections formula loses no information: its comparison at `X` is injective. -/
private theorem zariskiSectionsIso_injective (X : BigZariskiOver B S.obj S.property) :
    Function.Injective ((zariskiInverseImageSectionsIso B S X).hom.app F) :=
  (mono_iff_injective _).mp inferInstance

/-- Restriction along a morphism of schemes over `S`, read through the sections formula, is the
canonical restriction map between the global sections of the small-site pullbacks. -/
private theorem zariskiSectionsIso_restriction
    {X Y : BigZariskiOver B S.obj S.property} (h : Y ⟶ X)
    (t : (zariskiInverseImagePresheaf B S F).obj (op X)) :
    zariskiPullbackSectionsRestriction B S h F
        ((zariskiInverseImageSectionsIso B S X).hom.app F t) =
      (zariskiInverseImageSectionsIso B S Y).hom.app F
        ((zariskiInverseImagePresheaf B S F).map h.op t) := by
  rw [← types_comp_apply, ← types_comp_apply, zariskiInverseImageSectionsIso_naturality B S h F]

/-- **The universal property of the equality locus.** Two sections of `π_S⁻¹F` over `X` have the
same restriction along `h : Y ⟶ X` exactly when the image of `Y` in `X` is contained in their
equality locus.

By Stacks 09XM the containment is equivalent to the two corresponding global sections of the
small-site pullback of `F` to `X` having the same inverse image along `h`, and by
`CategoryTheory.sheafPullbackSectionsRestriction_eq_iff` that is equivalent to their having the
same image under the sections-restriction map, which the sections formula identifies with
restriction in `π_S⁻¹F`. -/
public theorem forall_mem_zariskiInverseImageEqLocus_iff
    {X Y : BigZariskiOver B S.obj S.property}
    (t₁ t₂ : (zariskiInverseImagePresheaf B S F).obj (op X)) (h : Y ⟶ X) :
    (∀ y, (B.inclusion.map h.left).base y ∈ zariskiInverseImageEqLocus B S F X t₁ t₂) ↔
      (zariskiInverseImagePresheaf B S F).map h.op t₁ =
        (zariskiInverseImagePresheaf B S F).map h.op t₂ := by
  have h1 : (∀ y, (B.inclusion.map h.left).base y ∈
        zariskiInverseImageEqLocus B S F X t₁ t₂) ↔
      (smallZariskiSitePullback B h.left).map (zariskiInverseImageSectionHom B S F X t₁) =
        (smallZariskiSitePullback B h.left).map (zariskiInverseImageSectionHom B S F X t₂) :=
    (smallZariskiPullback_map_eq_iff B X.left h.left terminalIsTerminal
      (zariskiInverseImageSectionHom B S F X t₁)
      (zariskiInverseImageSectionHom B S F X t₂)).symm
  have h2 : zariskiPullbackSectionsRestriction B S h F
        ((zariskiInverseImageSectionsIso B S X).hom.app F t₁) =
      zariskiPullbackSectionsRestriction B S h F
        ((zariskiInverseImageSectionsIso B S X).hom.app F t₂) ↔
      (smallZariskiSitePullback B h.left).map (zariskiInverseImageSectionHom B S F X t₁) =
        (smallZariskiSitePullback B h.left).map (zariskiInverseImageSectionHom B S F X t₂) :=
    sheafPullbackSectionsRestriction_eq_iff
      (SmallZariski.topology B S.obj S.property)
      (SmallZariski.topology B X.left.obj X.left.property)
      (SmallZariski.topology B Y.left.obj Y.left.property)
      (smallZariskiBaseChange B X.hom) (smallZariskiBaseChange B h.left)
      (smallZariskiBaseChange B Y.hom)
      (smallZariskiBaseChange_compIso B h.left X.hom ≪≫
        eqToIso (congrArg (smallZariskiBaseChange B) (Over.w h)))
      (SmallZariski.finalIsTerminal B X.left.obj X.left.property)
      (smallZariskiBaseChange_finalIsTerminal B h.left) F _ _
  refine h1.trans (h2.symm.trans ?_)
  rw [zariskiSectionsIso_restriction, zariskiSectionsIso_restriction]
  exact (zariskiSectionsIso_injective B S F Y).eq_iff

/-! ### Open subschemes as objects of the big Zariski site over `S` -/

/-- A morphism of a big Zariski site factors through an open subscheme of its target exactly
when its image is contained in that open. -/
public theorem BigZariskiSite.exists_factor_iff_forall_mem {X Y : B.Schemes} (f : Y ⟶ X)
    (V : (B.inclusion.obj X).Opens) :
    (∃ q : B.inclusion.obj Y ⟶ V.toScheme, q ≫ V.ι = B.inclusion.map f) ↔
      ∀ y, (B.inclusion.map f) y ∈ V := by
  constructor
  · rintro ⟨q, hq⟩ y
    rw [← hq, Scheme.Hom.comp_apply]
    exact (q y).property
  · intro hy
    refine ⟨(B.inclusion.obj Y).topIso.inv ≫
      (B.inclusion.map f).resLE V ⊤
        (fun y _ => (Scheme.Hom.mem_preimage _).mpr (hy y)), ?_⟩
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      (B.inclusion.obj Y).toIso_inv_ι, Category.id_comp]

/-- An open subscheme of an object of a big Zariski site, as an object of that site: a big
Zariski site is closed under passing to open subschemes, because an open subscheme is no larger
than the scheme it sits in. -/
public def BigZariskiSite.openObj {X : B.Schemes} (V : (B.inclusion.obj X).Opens) : B.Schemes :=
  ⟨V.toScheme, (Scheme.size_coe_opens_le (B.inclusion.obj X) V).trans_lt X.property⟩

/-- The inclusion of an open subscheme, as a morphism of the big Zariski site. -/
public def BigZariskiSite.openObjι {X : B.Schemes} (V : (B.inclusion.obj X).Opens) :
    BigZariskiSite.openObj B V ⟶ X := ObjectProperty.homMk V.ι

/-- An open subscheme of an object `X` of the big Zariski site over `S`, as an object over `S`
through the inclusion into `X`. -/
public def BigZariskiOver.openObj {X : BigZariskiOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens) : BigZariskiOver B S.obj S.property :=
  Over.mk (BigZariskiSite.openObjι B V ≫ X.hom)

/-- The inclusion of an open subscheme of `X`, as a morphism of schemes over `S`. -/
public def BigZariskiOver.openObjι {X : BigZariskiOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens) : BigZariskiOver.openObj B S V ⟶ X :=
  Over.homMk (BigZariskiSite.openObjι B V) rfl

/-- On points, the inclusion of an open subscheme of `X` is the inclusion of that open. -/
public theorem BigZariskiOver.openObjι_apply {X : BigZariskiOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens)
    (y : B.inclusion.obj (BigZariskiOver.openObj B S V).left) :
    (B.inclusion.map (BigZariskiOver.openObjι B S V).left) y = V.ι y := rfl

/-- An open of `X` is contained in another as soon as every point of the first, viewed through
the inclusion of the corresponding object over `S`, lies in the second. -/
public theorem BigZariskiOver.le_of_forall_openObjι_mem
    {X : BigZariskiOver B S.obj S.property} (V W : (B.inclusion.obj X.left).Opens)
    (h : ∀ y, (B.inclusion.map (BigZariskiOver.openObjι B S V).left) y ∈ W) : V ≤ W :=
  fun _ hx => h ⟨_, hx⟩

/-- On points, the inclusion of an open subscheme of `Y` followed by `h : Y ⟶ X` is the
inclusion followed by `h`. -/
public theorem BigZariskiOver.openObjι_comp_apply {X Y : BigZariskiOver B S.obj S.property}
    (V : (B.inclusion.obj Y.left).Opens) (h : Y ⟶ X)
    (y : B.inclusion.obj (BigZariskiOver.openObj B S V).left) :
    (B.inclusion.map (BigZariskiOver.openObjι B S V ≫ h).left) y =
      (B.inclusion.map h.left) ((B.inclusion.map (BigZariskiOver.openObjι B S V).left) y) := by
  rw [← Scheme.Hom.comp_apply]
  rfl

/-- On points, a composite of morphisms of the big Zariski site over `S` acts as the composite
of the actions of its factors. -/
public theorem BigZariskiOver.inclusion_map_comp_apply
    {X Y Z : BigZariskiOver B S.obj S.property} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : B.inclusion.obj X.left) :
    B.inclusion.map (f ≫ g).left w = B.inclusion.map g.left (B.inclusion.map f.left w) := by
  rw [← Scheme.Hom.comp_apply]
  rfl

/-- **The equality locus is compatible with restriction.** The equality locus of the
restrictions of two sections of `π_S⁻¹F` along `h : Y ⟶ X` is the inverse image of their
equality locus.

Both inclusions are obtained by testing the universal property against the inclusion of the
relevant open subscheme of `Y`, viewed as an object of the big Zariski site over `S`: the
equality locus of the restrictions identifies the two sections after restriction along that
inclusion, hence along its composite with `h`, and conversely. -/
public theorem zariskiInverseImageEqLocus_preimage
    {X Y : BigZariskiOver B S.obj S.property}
    (t₁ t₂ : (zariskiInverseImagePresheaf B S F).obj (op X)) (h : Y ⟶ X) :
    B.inclusion.map h.left ⁻¹ᵁ zariskiInverseImageEqLocus B S F X t₁ t₂ =
      zariskiInverseImageEqLocus B S F Y ((zariskiInverseImagePresheaf B S F).map h.op t₁)
        ((zariskiInverseImagePresheaf B S F).map h.op t₂) := by
  refine le_antisymm (BigZariskiOver.le_of_forall_openObjι_mem B S _ _ ?_)
    (BigZariskiOver.le_of_forall_openObjι_mem B S _ _ ?_)
  · refine (forall_mem_zariskiInverseImageEqLocus_iff B S F _ _
      (BigZariskiOver.openObjι B S (B.inclusion.map h.left ⁻¹ᵁ
        zariskiInverseImageEqLocus B S F X t₁ t₂))).mpr ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
    refine (forall_mem_zariskiInverseImageEqLocus_iff B S F t₁ t₂ _).mp fun y => ?_
    rw [BigZariskiOver.openObjι_comp_apply, BigZariskiOver.openObjι_apply]
    exact y.property
  · intro y
    rw [Scheme.Hom.mem_preimage, ← BigZariskiOver.openObjι_comp_apply]
    refine (forall_mem_zariskiInverseImageEqLocus_iff B S F t₁ t₂ _).mpr ?_ y
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact (forall_mem_zariskiInverseImageEqLocus_iff B S F _ _
      (BigZariskiOver.openObjι B S (zariskiInverseImageEqLocus B S F Y
        ((zariskiInverseImagePresheaf B S F).map h.op t₁)
        ((zariskiInverseImagePresheaf B S F).map h.op t₂)))).mp fun z =>
      z.property

/-- **The equality locus is everything exactly when the two sections agree.** This is the
universal property at the identity of `X`. -/
public theorem zariskiInverseImageEqLocus_eq_top_iff {X : BigZariskiOver B S.obj S.property}
    (t₁ t₂ : (zariskiInverseImagePresheaf B S F).obj (op X)) :
    zariskiInverseImageEqLocus B S F X t₁ t₂ = ⊤ ↔ t₁ = t₂ := by
  constructor
  · intro hW
    simpa using (forall_mem_zariskiInverseImageEqLocus_iff B S F t₁ t₂ (𝟙 X)).mp fun y => by
      rw [hW]
      trivial
  · rintro rfl
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    exact (forall_mem_zariskiInverseImageEqLocus_iff B S F t₁ t₁ (𝟙 X)).mpr rfl y

/-- **Geometric uniqueness on the big Zariski site.** Two sections of `π_S⁻¹F` over `Y` which
have the same restriction along every member of a family of morphisms that is jointly
surjective on points are equal.

By `AlgebraicGeometry.forall_mem_zariskiInverseImageEqLocus_iff` the image of each member of
the family lies in the equality locus of the two sections, so joint surjectivity makes the
equality locus all of `Y`. -/
public theorem eq_of_zariskiInverseImage_map_eq_of_jointlySurjective
    {Y : BigZariskiOver B S.obj S.property}
    (t₁ t₂ : (zariskiInverseImagePresheaf B S F).obj (op Y))
    {K : Type v} (W : K → BigZariskiOver B S.obj S.property) (g : ∀ k, W k ⟶ Y)
    (hsurj : ∀ y : B.inclusion.obj Y.left, ∃ k, y ∈ Set.range (B.inclusion.map (g k).left))
    (h : ∀ k, (zariskiInverseImagePresheaf B S F).map (g k).op t₁ =
      (zariskiInverseImagePresheaf B S F).map (g k).op t₂) :
    t₁ = t₂ := by
  refine (zariskiInverseImageEqLocus_eq_top_iff B S F t₁ t₂).mp
    (TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_))
  obtain ⟨k, z, hz⟩ := hsurj y
  rw [← hz]
  exact (forall_mem_zariskiInverseImageEqLocus_iff B S F t₁ t₂ (g k)).mpr (h k) z

/-- **The uniqueness half of the fpqc sheaf condition of Stacks 09XN, Zariski case.** Two
sections of `π_S⁻¹F` over an object `X` of the big Zariski site over `S` which agree on the
members of an fpqc covering presieve of `X` are equal, because an fpqc covering family is
jointly surjective. -/
public theorem smallZariskiProjection_inverseImage_isSeparatedFor_fpqc
    {X : BigZariskiOver B S.obj S.property} (R : Presieve X)
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X) :
    Presieve.IsSeparatedFor (zariskiInverseImagePresheaf B S F) R := by
  obtain ⟨ι, Z, p, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  intro x t₁ t₂ h₁ h₂
  exact eq_of_zariskiInverseImage_map_eq_of_jointlySurjective B S F t₁ t₂ Z p
    (fpqc_jointly_surjective _ hR)
    fun i => (h₁ (p i) (.mk i)).trans (h₂ (p i) (.mk i)).symm

/-! ### Descent of the equality loci along an fpqc covering -/

/-- The fibre product of two members of a family of schemes over `X`, as an object of the big
Zariski site over `S`. -/
public def BigZariskiOver.pairProduct {X : BigZariskiOver B S.obj S.property}
    {Y Z : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigZariskiOver B S.obj S.property :=
  Over.mk (Limits.pullback.fst f.left g.left ≫ Y.hom)

/-- The first projection of the fibre product of two members of a family over `X`. -/
public def BigZariskiOver.pairProductFst {X : BigZariskiOver B S.obj S.property}
    {Y Z : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigZariskiOver.pairProduct B S f g ⟶ Y :=
  Over.homMk (Limits.pullback.fst f.left g.left) rfl

/-- The second projection of the fibre product of two members of a family over `X`. -/
public def BigZariskiOver.pairProductSnd {X : BigZariskiOver B S.obj S.property}
    {Y Z : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigZariskiOver.pairProduct B S f g ⟶ Z :=
  Over.homMk (Limits.pullback.snd f.left g.left) (by
    have hY : f.left ≫ X.hom = Y.hom := Over.w f
    have hZ : g.left ≫ X.hom = Z.hom := Over.w g
    change Limits.pullback.snd f.left g.left ≫ Z.hom =
      Limits.pullback.fst f.left g.left ≫ Y.hom
    rw [← hY, ← hZ, ← Category.assoc, ← Category.assoc, Limits.pullback.condition])

/-- The two projections of the fibre product agree over `X`. -/
public theorem BigZariskiOver.pairProduct_condition {X : BigZariskiOver B S.obj S.property}
    {Y Z : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigZariskiOver.pairProductFst B S f g ≫ f = BigZariskiOver.pairProductSnd B S f g ≫ g :=
  Over.OverMorphism.ext Limits.pullback.condition

/-- The morphism into the fibre product determined by a pair of morphisms agreeing over the
base. -/
public def BigZariskiOver.pairLift {X Y Z W : BigZariskiOver B S.obj S.property} (f : Y ⟶ X)
    (g : Z ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    W ⟶ BigZariskiOver.pairProduct B S f g :=
  Over.homMk (Limits.pullback.lift a.left b.left (congrArg Over.Hom.left hab)) (by
    change Limits.pullback.lift a.left b.left (congrArg Over.Hom.left hab) ≫
      Limits.pullback.fst f.left g.left ≫ Y.hom = W.hom
    rw [← Category.assoc, Limits.pullback.lift_fst]
    exact Over.w a)

/-- The lift into the fibre product recovers its first component. -/
public theorem BigZariskiOver.pairLift_fst
    {X Y Z W : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) (a : W ⟶ Y)
    (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    BigZariskiOver.pairLift B S f g a b hab ≫
      BigZariskiOver.pairProductFst B S f g = a :=
  Over.OverMorphism.ext (Limits.pullback.lift_fst _ _ _)

/-- The lift into the fibre product recovers its second component. -/
public theorem BigZariskiOver.pairLift_snd
    {X Y Z W : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) (a : W ⟶ Y)
    (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    BigZariskiOver.pairLift B S f g a b hab ≫
      BigZariskiOver.pairProductSnd B S f g = b :=
  Over.OverMorphism.ext (Limits.pullback.lift_snd _ _ _)

/-- Two points of `Y` and `Z` with the same image in `X` come from a common point of the fibre
product `Y ×_X Z`. -/
private theorem BigZariskiOver.exists_pairProduct_point
    {X Y Z : BigZariskiOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X)
    (y : B.inclusion.obj Y.left) (z : B.inclusion.obj Z.left)
    (h : B.inclusion.map f.left y = B.inclusion.map g.left z) :
    ∃ w : B.inclusion.obj (BigZariskiOver.pairProduct B S f g).left,
      B.inclusion.map (BigZariskiOver.pairProductFst B S f g).left w = y ∧
        B.inclusion.map (BigZariskiOver.pairProductSnd B S f g).left w = z := by
  obtain ⟨w, hy, hz⟩ := Scheme.Pullback.exists_preimage_pullback y z h
  refine ⟨(PreservesPullback.iso B.inclusion f.left g.left).inv w, ?_, ?_⟩
  · rw [← hy, ← PreservesPullback.iso_inv_fst B.inclusion f.left g.left,
      Scheme.Hom.comp_apply]
    rfl
  · rw [← hz, ← PreservesPullback.iso_inv_snd B.inclusion f.left g.left,
      Scheme.Hom.comp_apply]
    rfl

/-- A jointly surjective family stays jointly surjective after base change: first projections
version. -/
public theorem BigZariskiOver.exists_mem_range_pairProductFst
    {X W : BigZariskiOver B S.obj S.property} (q : W ⟶ X)
    {K : Type v} (V : K → BigZariskiOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
    (hsurj : ∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left))
    (w : B.inclusion.obj W.left) :
    ∃ k, w ∈ Set.range (B.inclusion.map (BigZariskiOver.pairProductFst B S q (v k)).left) := by
  obtain ⟨k, z, hz⟩ := hsurj ((B.inclusion.map q.left) w)
  obtain ⟨y, hy, -⟩ := BigZariskiOver.exists_pairProduct_point B S q (v k) w z hz.symm
  exact ⟨k, y, hy⟩

/-- A jointly surjective family stays jointly surjective after base change: second projections
version. -/
public theorem BigZariskiOver.exists_mem_range_pairProductSnd
    {X Z : BigZariskiOver B S.obj S.property} (r : Z ⟶ X)
    {K : Type v} (V : K → BigZariskiOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
    (hsurj : ∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left))
    (z : B.inclusion.obj Z.left) :
    ∃ k, z ∈ Set.range (B.inclusion.map (BigZariskiOver.pairProductSnd B S (v k) r).left) := by
  obtain ⟨k, y, hy⟩ := hsurj ((B.inclusion.map r.left) z)
  obtain ⟨w, -, hw⟩ := BigZariskiOver.exists_pairProduct_point B S (v k) r y z hy
  exact ⟨k, w, hw⟩

/-- **Stacks 09XN, step 4: the equality loci of a compatible family descend.** Let
`{p i : Z i ⟶ X}` be a family of schemes over `S` whose underlying family of morphisms of
schemes is an fpqc covering of `X`, let `x i` be a compatible family of sections of `π_S⁻¹F`
over the `Z i`, and let `t` be a section of `π_S⁻¹F` over `X`. Then the open loci on which
`x i` agrees with the restriction of `t` come from a unique open of `X`.

The loci pull back to the same open on each fibre product `Z i ×_X Z j`: by
`AlgebraicGeometry.zariskiInverseImageEqLocus_preimage` the two inverse images are the equality
loci of the restricted sections, the restrictions of `x i` and `x j` agree there by
compatibility, and the restrictions of `t` agree there because the two projections agree over
`X`. Stacks 03N0 then descends them. -/
public theorem existsUnique_preimage_eq_zariskiInverseImageEqLocus
    {X : BigZariskiOver B S.obj S.property} {I : Type v}
    (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X)
    (x : ∀ i, (zariskiInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p x)
    (t : (zariskiInverseImagePresheaf B S F).obj (op X)) :
    ∃! V : (B.inclusion.obj X.left).Opens, ∀ i,
      B.inclusion.map (p i).left ⁻¹ᵁ V =
        zariskiInverseImageEqLocus B S F (Z i) (x i)
          ((zariskiInverseImagePresheaf B S F).map (p i).op t) := by
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hp
  refine existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage
    (fun i => B.inclusion.obj (Z i).left) (fun i => B.inclusion.map (p i).left) hp
    (fun i => zariskiInverseImageEqLocus B S F (Z i) (x i)
      ((zariskiInverseImagePresheaf B S F).map (p i).op t)) fun i j => ?_
  have hcond := BigZariskiOver.pairProduct_condition B S (p i) (p j)
  have hkey : B.inclusion.map (Limits.pullback.fst (p i).left (p j).left) ⁻¹ᵁ
        zariskiInverseImageEqLocus B S F (Z i) (x i)
          ((zariskiInverseImagePresheaf B S F).map (p i).op t) =
      B.inclusion.map (Limits.pullback.snd (p i).left (p j).left) ⁻¹ᵁ
        zariskiInverseImageEqLocus B S F (Z j) (x j)
          ((zariskiInverseImagePresheaf B S F).map (p j).op t) := by
    have h1 := zariskiInverseImageEqLocus_preimage B S F (x i)
      ((zariskiInverseImagePresheaf B S F).map (p i).op t)
      (BigZariskiOver.pairProductFst B S (p i) (p j))
    have h2 := zariskiInverseImageEqLocus_preimage B S F (x j)
      ((zariskiInverseImagePresheaf B S F).map (p j).op t)
      (BigZariskiOver.pairProductSnd B S (p i) (p j))
    rw [hx i j (BigZariskiOver.pairProduct B S (p i) (p j))
      (BigZariskiOver.pairProductFst B S (p i) (p j))
      (BigZariskiOver.pairProductSnd B S (p i) (p j)) hcond, ← Functor.map_comp_apply, ← op_comp,
      hcond] at h1
    rw [← Functor.map_comp_apply, ← op_comp] at h2
    exact h1.trans h2.symm
  rw [← PreservesPullback.iso_inv_fst B.inclusion (p i).left (p j).left,
    ← PreservesPullback.iso_inv_snd B.inclusion (p i).left (p j).left,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hkey]

/-! ### The existence half, reduced to local representability -/

/-- If a section over `V` agrees with a section over `Z` on `V ×_X Z`, then the two agree after
any pair of morphisms into `V` and `Z` which agree over `X`: such a pair factors through the
fibre product. -/
private theorem zariskiInverseImage_map_eq_of_agree_on_pairProduct
    {X V Z W : BigZariskiOver B S.obj S.property}
    (f : V ⟶ X) (g : Z ⟶ X) (tV : (zariskiInverseImagePresheaf B S F).obj (op V))
    (tZ : (zariskiInverseImagePresheaf B S F).obj (op Z))
    (hagree : (zariskiInverseImagePresheaf B S F).map
        (BigZariskiOver.pairProductFst B S f g).op tV =
      (zariskiInverseImagePresheaf B S F).map
        (BigZariskiOver.pairProductSnd B S f g).op tZ)
    (a : W ⟶ V) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    (zariskiInverseImagePresheaf B S F).map a.op tV =
      (zariskiInverseImagePresheaf B S F).map b.op tZ := by
  rw [← BigZariskiOver.pairLift_fst B S f g a b hab, op_comp, Functor.map_comp_apply, hagree,
    ← Functor.map_comp_apply, ← op_comp, BigZariskiOver.pairLift_snd]

/-- **Stacks 09XN, steps 4 and 5: the existence half from local representability.** Suppose
that every compatible family of sections of `π_S⁻¹F` on an fpqc covering of an object `X` of
the big Zariski site over `S` is *locally represented*: there is a family `{v k : V k ⟶ X}`
which generates a covering sieve of the big Zariski topology and is jointly surjective on
points, together with sections `t k` of `π_S⁻¹F` over `V k`, such that `t k` agrees with every
member of the family on the fibre products `V k ×_X Z i`. Then every compatible family of
sections of `π_S⁻¹F` on an fpqc covering has an amalgamation.

The sections `t k` form a compatible family for `{v k}`: any two of them agree after being
pulled back to a common object `W` over `X`, because they both agree there with every member
of the original family, and the base changes of the original fpqc covering to `W` are jointly
surjective, so geometric uniqueness applies. Since `π_S⁻¹F` is a sheaf for the big Zariski
topology the `t k` glue to a section `t` over `X`, and the same geometric uniqueness argument
— now along the base changes of `{v k}` — identifies the restriction of `t` with each member
of the family. -/
public theorem exists_isAmalgamation_of_locallyRepresentable_zariski
    (hrep : ∀ (X : BigZariskiOver B S.obj S.property) (I : Type (u + 1))
      (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X),
      Presieve.ofArrows Z p ∈
        Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X →
      ∀ x : ∀ i, (zariskiInverseImagePresheaf B S F).obj (op (Z i)),
      Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p x →
      ∃ (K : Type (u + 1)) (V : K → BigZariskiOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
        (t : ∀ k, (zariskiInverseImagePresheaf B S F).obj (op (V k))),
        Sieve.generate (Presieve.ofArrows V v) ∈
            BigZariskiOver.topology B S.obj S.property X ∧
          (∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left)) ∧
          ∀ k i, (zariskiInverseImagePresheaf B S F).map
                (BigZariskiOver.pairProductFst B S (v k) (p i)).op (t k) =
            (zariskiInverseImagePresheaf B S F).map
              (BigZariskiOver.pairProductSnd B S (v k) (p i)).op (x i))
    {X : BigZariskiOver B S.obj S.property} (R : Presieve X)
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X)
    (y : Presieve.FamilyOfElements (zariskiInverseImagePresheaf B S F) R) (hy : y.Compatible) :
    ∃ t, y.IsAmalgamation t := by
  obtain ⟨I, Z, p, rfl⟩ := R.exists_eq_ofArrows
  have hxA : Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p
      (fun i => y (p i) (Presieve.ofArrows.mk i)) :=
    fun i j W gi gj hg => hy gi gj (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) hg
  obtain ⟨K, V, v, t, hsieve, hsurjV, hagree⟩ := hrep X I Z p hR _ hxA
  have hsurjZ : ∀ z : B.inclusion.obj X.left,
      ∃ i, z ∈ Set.range (B.inclusion.map (p i).left) := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
    exact fpqc_jointly_surjective _ hR
  have htA : Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) v t := by
    intro k l W g₁ g₂ hg
    refine eq_of_zariskiInverseImage_map_eq_of_jointlySurjective B S F _ _
      (fun i => BigZariskiOver.pairProduct B S (g₁ ≫ v k) (p i))
      (fun i => BigZariskiOver.pairProductFst B S (g₁ ≫ v k) (p i))
      (BigZariskiOver.exists_mem_range_pairProductFst B S (g₁ ≫ v k) Z p hsurjZ) fun i => ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hcond := BigZariskiOver.pairProduct_condition B S (g₁ ≫ v k) (p i)
    refine (zariskiInverseImage_map_eq_of_agree_on_pairProduct B S F (v k) (p i) (t k) _
      (hagree k i) _ _
      ((Category.assoc _ _ _).trans hcond)).trans ?_
    exact (zariskiInverseImage_map_eq_of_agree_on_pairProduct B S F (v l) (p i) (t l) _
      (hagree l i) _ _
      ((Category.assoc _ _ _).trans ((_ ≫= hg.symm).trans hcond))).symm
  have hPsheaf : Presieve.IsSheaf (BigZariskiOver.topology B S.obj S.property)
      (zariskiInverseImagePresheaf B S F) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((smallZariskiProjection B S).inverseImage.obj F).property
  have hsheaf : (Presieve.ofArrows V v).IsSheafFor (zariskiInverseImagePresheaf B S F) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hPsheaf _ hsieve
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff
    (P := zariskiInverseImagePresheaf B S F) (π := v)).mp hsheaf t htA
  refine ⟨s, ?_⟩
  rw [Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows]
  intro i
  refine eq_of_zariskiInverseImage_map_eq_of_jointlySurjective B S F _ _
    (fun k => BigZariskiOver.pairProduct B S (v k) (p i))
    (fun k => BigZariskiOver.pairProductSnd B S (v k) (p i))
    (BigZariskiOver.exists_mem_range_pairProductSnd B S (p i) V v hsurjV) fun k => ?_
  rw [← Functor.map_comp_apply, ← op_comp,
    ← BigZariskiOver.pairProduct_condition B S (v k) (p i), op_comp,
    Functor.map_comp_apply, hs k]
  exact hagree k i

end Relative

/-- A presheaf on the big Zariski category over `S` is a sheaf for the fpqc topology as soon as
it satisfies the sheaf condition for every fpqc covering presieve. -/
public theorem bigZariskiOver_isSheaf_fpqc_of_isSheafFor (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {P : (BigZariskiOver B S hS)ᵒᵖ ⥤ Type w}
    (h : ∀ ⦃X : BigZariskiOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S hS) X →
      Presieve.IsSheafFor P R) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S hS)).toGrothendieck) P := by
  have : PreservesLimitsOfShape WalkingCospan (BigZariskiOver.toScheme B S hS) := by
    infer_instance
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  exact h

/-- **Stacks 09XN, the fpqc sheaf condition from local representability, Zariski case.** The
presheaf `X ↦ Γ(X_Zar, f_X⁻¹F)` on the big Zariski site over `S` — the underlying presheaf of
`π_S⁻¹F` — is a sheaf for the fpqc topology as soon as every compatible family of its sections
on an fpqc covering is locally represented by sections over a big-Zariski covering of the base,
in the sense of
`AlgebraicGeometry.exists_isAmalgamation_of_locallyRepresentable_zariski`.

The uniqueness half is
`AlgebraicGeometry.smallZariskiProjection_inverseImage_isSeparatedFor_fpqc`, which is
unconditional; local representability is the only remaining input, and it is the step in the
proof of Stacks 09XN which produces, after a Zariski refinement of the covering, an open
subscheme of `S` and a section of `F` over it representing a given local section. -/
public theorem smallZariskiProjection_inverseImage_isSheaf_fpqc_of_locallyRepresentable
    (B : BigZariskiSite.{u}) (S : B.Schemes)
    (F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)))
    (hrep : ∀ (X : BigZariskiOver B S.obj S.property) (I : Type (u + 1))
      (Z : I → BigZariskiOver B S.obj S.property) (p : ∀ i, Z i ⟶ X),
      Presieve.ofArrows Z p ∈
        Scheme.fpqcPrecoverage.comap (BigZariskiOver.toScheme B S.obj S.property) X →
      ∀ x : ∀ i, (zariskiInverseImagePresheaf B S F).obj (op (Z i)),
      Presieve.Arrows.Compatible (zariskiInverseImagePresheaf B S F) p x →
      ∃ (K : Type (u + 1)) (V : K → BigZariskiOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
        (t : ∀ k, (zariskiInverseImagePresheaf B S F).obj (op (V k))),
        Sieve.generate (Presieve.ofArrows V v) ∈
            BigZariskiOver.topology B S.obj S.property X ∧
          (∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left)) ∧
          ∀ k i, (zariskiInverseImagePresheaf B S F).map
                (BigZariskiOver.pairProductFst B S (v k) (p i)).op (t k) =
            (zariskiInverseImagePresheaf B S F).map
              (BigZariskiOver.pairProductSnd B S (v k) (p i)).op (x i)) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap
        (BigZariskiOver.toScheme B S.obj S.property)).toGrothendieck)
      ((smallZariskiProjection B S).inverseImage.obj F).obj := by
  refine bigZariskiOver_isSheaf_fpqc_of_isSheafFor B S.obj S.property ?_
  intro X R hR
  exact (smallZariskiProjection_inverseImage_isSeparatedFor_fpqc B S F R hR).isSheafFor
    (exists_isAmalgamation_of_locallyRepresentable_zariski B S F hrep R hR)

end AlgebraicGeometry

end
