module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcSheaf
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsReflection

/-!
# The existence half of the fpqc sheaf condition for a sheaf pulled back from the small étale site

Let `S` be a scheme in a big étale site `B`, let `F` be a sheaf of sets on the small étale site
of `S`, and let `π_S⁻¹F` be its inverse image along the projection from the big étale topos
over `S`. The uniqueness half of the fpqc sheaf condition for `π_S⁻¹F` is unconditional
(`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc`); this file proves
the existence half from one remaining geometric input, the *local representability* of
compatible families, and so reduces the fpqc sheaf condition of Stacks 09XN to that input.

The tool is an equality locus on the big site. Two sections of `π_S⁻¹F` over an object `X` of
the big étale site over `S` agree on a largest open subscheme of `X`: there is an open `W ⊆ X`
such that a morphism `h : Y ⟶ X` of schemes over `S` factors through `W` exactly when the two
sections have the same restriction along `h`. This is Stacks 09XM read on the big site. Its
decisive property is that it is compatible with restriction, and because it is phrased in terms
of the *presheaf* `π_S⁻¹F`, whose restriction maps compose on the nose, that compatibility
needs no comparison of iterated inverse images on small étale sites.

Two consequences carry the proof. First, two sections of `π_S⁻¹F` which agree along a family of
morphisms that is jointly surjective on points are equal — geometric uniqueness, with no
flatness or quasi-compactness needed. Second, the equality loci of a compatible family on an
fpqc covering descend, by Stacks 03N0, to a single open of the base: this is the first
paragraph of the proof of Stacks 09XN.

Granted local representability — after a refinement generating a big étale covering, every
compatible family is given by sections over the members of that covering, agreeing with the
original family on the fibre products — the existence of an amalgamation follows: the local
sections are themselves a compatible family for the refined covering by geometric uniqueness,
they glue because `π_S⁻¹F` is a sheaf for the big étale topology, and the glued section
restricts to the original family again by geometric uniqueness.

## Main definitions

* `AlgebraicGeometry.etaleInverseImageEqLocus` — the largest open of `X` on which two sections of
  `π_S⁻¹F` over `X` agree.
* `AlgebraicGeometry.BigEtaleOver.pairProduct` — the fibre product of two objects over `X` in
  the big étale site over `S`, with its two projections
  `AlgebraicGeometry.BigEtaleOver.pairProductFst` and
  `AlgebraicGeometry.BigEtaleOver.pairProductSnd`.

## Main results

* `AlgebraicGeometry.factorsThrough_etaleInverseImageEqLocus_iff` and
  `AlgebraicGeometry.forall_mem_etaleInverseImageEqLocus_iff` — the universal property of the
  equality locus, by factorizations and by points.
* `AlgebraicGeometry.etaleInverseImageEqLocus_preimage` — the equality locus is compatible with
  restriction.
* `AlgebraicGeometry.etaleInverseImageEqLocus_eq_top_iff` — the equality locus is everything
  exactly when the two sections agree.
* `AlgebraicGeometry.eq_of_etaleInverseImage_map_eq_of_jointlySurjective` — geometric
  uniqueness of sections of `π_S⁻¹F` along a jointly surjective family.
* `AlgebraicGeometry.existsUnique_preimage_eq_etaleInverseImageEqLocus` — **Stacks 09XN,
  step 4**: the equality loci of a compatible family on an fpqc covering descend to the base.
* `AlgebraicGeometry.exists_isAmalgamation_of_locallyRepresentable` and
  `AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_locallyRepresentable` —
  the existence half, and hence the whole fpqc sheaf condition, from local representability.

## Implementation notes

The sections formula `AlgebraicGeometry.etaleInverseImageSectionsIso` turns a section of
`π_S⁻¹F` over `X` into a global section of the small-site pullback of `F` to `X`, presented as
a morphism out of a terminal sheaf by `CategoryTheory.Sheaf.ΓEquivHomTerminal`; the equality
locus is the open of Stacks 09XM attached to the resulting pair of global sections. What makes
the universal property an equivalence rather than an implication is
`CategoryTheory.sheafPullbackSectionsRestriction_eq_iff`: restriction along `h` in the presheaf
`π_S⁻¹F` corresponds, under the sections formula, to the sections-restriction map of the
small-site pullbacks, and that map has exactly the same fibres as inverse image along `h`.

Compatibility with restriction is proved by testing both opens against the morphisms out of
their own open subschemes, which are objects of the big étale site over `S` because the site is
closed under passing to opens. The hypothesis of the universal property is a factorization of
the underlying morphism of schemes, so one inclusion is read off from
`AlgebraicGeometry.Scheme.Hom.resLE` and the other from the identity.

Fibre products are taken in the size-bounded category of schemes of `B` and equipped with a
structure morphism by hand rather than formed in the slice category, so that their projections
are literally the projections of the underlying fibre product of schemes; Stacks 03N0 is stated
for the fibre product of schemes, and the two are compared by
`CategoryTheory.Limits.PreservesPullback.iso`.

Local representability is the hypothesis `hrep`. It is not vacuous: taking the refined covering
to be the given fpqc covering itself satisfies every clause except that an fpqc covering need
not generate a covering sieve of the big étale topology, which is precisely the content of the
étale refinement step in the proof of Stacks 09XN. That step rests on the description of
`g⁻¹𝒢` as a sheafified left Kan extension, which is what remains to be formalized.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

section Relative

variable (B : BigEtaleSite.{u}) (S : B.Scheme)
  (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))

/-- The presheaf on the big étale site over `S` underlying `π_S⁻¹F`. By the sections formula
`AlgebraicGeometry.etaleInverseImageSectionsIso` it is `X ↦ Γ(X_ét, f_X⁻¹F)`. -/
public abbrev etaleInverseImagePresheaf : (BigEtaleOver B S.obj S.property)ᵒᵖ ⥤ Type (u + 1) :=
  ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj

/-- The pullback of `F` to the small étale site of an object `X` of the big étale site over
`S`, along the structure morphism of `X`. -/
public abbrev etaleSmallPullbackSheaf (X : BigEtaleOver B S.obj S.property) :
    Sheaf (SmallEtale.topology B X.left.obj X.left.property) (Type (u + 1)) :=
  ((smallEtaleBaseChange B X.hom).sheafPullback (Type (u + 1))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)).obj F

/-- A section of `π_S⁻¹F` over `X`, read through the sections formula as a morphism from the
terminal sheaf on the small étale site of `X` to the small-site pullback of `F` to `X`. -/
public def etaleInverseImageSectionHom (X : BigEtaleOver B S.obj S.property)
    (t : (etaleInverseImagePresheaf B S F).obj (op X)) :
    (⊤_ (Sheaf (SmallEtale.topology B X.left.obj X.left.property) (Type (u + 1)))) ⟶
      etaleSmallPullbackSheaf B S F X :=
  Sheaf.ΓEquivHomTerminal (SmallEtale.topology B X.left.obj X.left.property) _
    ((etaleInverseImageSectionsIso B S X).hom.app F t)

/-- **The equality locus of two sections of `π_S⁻¹F`.** The largest open subscheme of `X` on
which two sections of `π_S⁻¹F` over `X` agree, namely the open of Stacks 09XM attached to the
two corresponding global sections of the small-site pullback of `F` to `X`. -/
public def etaleInverseImageEqLocus (X : BigEtaleOver B S.obj S.property)
    (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op X)) : (B.inclusion.obj X.left).Opens :=
  openEqLocus.{u, u + 1} B X.left (etaleSmallPullbackSheaf B S F X)
    (etaleInverseImageSectionHom B S F X t₁) (etaleInverseImageSectionHom B S F X t₂)

/-- The equality locus is by definition the open of Stacks 09XM attached to the two
corresponding global sections of the small-site pullback. -/
private theorem etaleInverseImageEqLocus_def (X : BigEtaleOver B S.obj S.property)
    (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op X)) :
    etaleInverseImageEqLocus B S F X t₁ t₂ =
      openEqLocus.{u, u + 1} B X.left (etaleSmallPullbackSheaf B S F X)
        (etaleInverseImageSectionHom B S F X t₁) (etaleInverseImageSectionHom B S F X t₂) :=
  rfl

/-- The sections formula loses no information: its comparison at `X` is injective. -/
private theorem sectionsIso_injective (X : BigEtaleOver B S.obj S.property) :
    Function.Injective ((etaleInverseImageSectionsIso B S X).hom.app F) :=
  ((etaleInverseImageSectionsIso B S X).app F).toEquiv.injective

/-- Restriction along a morphism of schemes over `S`, read through the sections formula, is the
canonical restriction map between the global sections of the small-site pullbacks. -/
private theorem sectionsIso_restriction {X Y : BigEtaleOver B S.obj S.property} (h : Y ⟶ X)
    (t : (etaleInverseImagePresheaf B S F).obj (op X)) :
    etalePullbackSectionsRestriction B S h F
        ((etaleInverseImageSectionsIso B S X).hom.app F t) =
      (etaleInverseImageSectionsIso B S Y).hom.app F
        ((etaleInverseImagePresheaf B S F).map h.op t) := by
  rw [← types_comp_apply, ← types_comp_apply, etaleInverseImageSectionsIso_naturality B S h F]

/-- **The universal property of the equality locus.** A morphism `h : Y ⟶ X` of schemes over
`S` factors through the equality locus of two sections of `π_S⁻¹F` over `X` exactly when the
two sections have the same restriction along `h`.

By Stacks 09XM the factorization is equivalent to the two corresponding global sections of the
small-site pullback of `F` to `X` having the same inverse image along `h`, and by
`CategoryTheory.sheafPullbackSectionsRestriction_eq_iff` that is equivalent to their having the
same image under the sections-restriction map, which the sections formula identifies with
restriction in `π_S⁻¹F`. -/
public theorem factorsThrough_etaleInverseImageEqLocus_iff
    {X Y : BigEtaleOver B S.obj S.property}
    (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op X)) (h : Y ⟶ X) :
    (∃ q : B.inclusion.obj Y.left ⟶ (etaleInverseImageEqLocus B S F X t₁ t₂).toScheme,
        q ≫ (etaleInverseImageEqLocus B S F X t₁ t₂).ι = B.inclusion.map h.left) ↔
      (etaleInverseImagePresheaf B S F).map h.op t₁ =
        (etaleInverseImagePresheaf B S F).map h.op t₂ := by
  rw [etaleInverseImageEqLocus_def, factorsThrough_openEqLocus_iff.{u, u + 1} B X.left Y.left
    (etaleSmallPullbackSheaf B S F X) (etaleInverseImageSectionHom B S F X t₁)
    (etaleInverseImageSectionHom B S F X t₂) h.left]
  have key := fun s₁ s₂ => sheafPullbackSectionsRestriction_eq_iff
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)
    (SmallEtale.topology B Y.left.obj Y.left.property)
    (smallEtaleBaseChange B X.hom) (smallEtaleBaseChange B h.left)
    (smallEtaleBaseChange B Y.hom)
    ((smallEtaleBaseChange_compIso B Y.left X.left S h.left X.hom).val ≪≫
      eqToIso (congrArg (smallEtaleBaseChange B) (Over.w h)))
    (SmallEtale.finalIsTerminal B X.left.obj X.left.property)
    (smallEtaleBaseChange_finalIsTerminal B h.left) F s₁ s₂
  have e := Functor.sheafPullbackConstruction.sheafPullbackIso
    (smallEtaleBaseChange B h.left) (Type (u + 1))
    (SmallEtale.topology B X.left.obj X.left.property)
    (SmallEtale.topology B Y.left.obj Y.left.property)
  constructor
  · intro hmap
    refine sectionsIso_injective B S F Y ?_
    rw [← sectionsIso_restriction, ← sectionsIso_restriction]
    exact (key _ _).mpr (map_eq_of_natIso e.symm hmap)
  · intro hP
    exact map_eq_of_natIso e <| (key _ _).mp
      (show etalePullbackSectionsRestriction B S h F
            ((etaleInverseImageSectionsIso B S X).hom.app F t₁) =
          etalePullbackSectionsRestriction B S h F
            ((etaleInverseImageSectionsIso B S X).hom.app F t₂) by
        rw [sectionsIso_restriction, sectionsIso_restriction, hP])

/-! ### Open subschemes as objects of the big étale site over `S` -/

/-- A morphism of a big étale site factors through an open subscheme of its target exactly when
its image is contained in that open. -/
public theorem BigEtaleSite.exists_factor_iff_forall_mem {X Y : B.Scheme} (f : Y ⟶ X)
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

/-- **The universal property of the equality locus, in terms of points.** Two sections of
`π_S⁻¹F` over `X` have the same restriction along `h : Y ⟶ X` exactly when the image of `Y` in
`X` is contained in their equality locus. -/
public theorem forall_mem_etaleInverseImageEqLocus_iff {X Y : BigEtaleOver B S.obj S.property}
    (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op X)) (h : Y ⟶ X) :
    (∀ y, (B.inclusion.map h.left) y ∈ etaleInverseImageEqLocus B S F X t₁ t₂) ↔
      (etaleInverseImagePresheaf B S F).map h.op t₁ =
        (etaleInverseImagePresheaf B S F).map h.op t₂ :=
  (BigEtaleSite.exists_factor_iff_forall_mem B h.left
      (etaleInverseImageEqLocus B S F X t₁ t₂)).symm.trans
    (factorsThrough_etaleInverseImageEqLocus_iff B S F t₁ t₂ h)

/-- An open subscheme of an object of a big étale site, as an object of that site: a big étale
site is closed under passing to open subschemes, because an open subscheme is no larger than
the scheme it sits in. -/
public def BigEtaleSite.openObj {X : B.Scheme} (V : (B.inclusion.obj X).Opens) : B.Scheme :=
  ⟨V.toScheme, (Scheme.size_coe_opens_le (B.inclusion.obj X) V).trans_lt X.property⟩

/-- The inclusion of an open subscheme, as a morphism of the big étale site. -/
public def BigEtaleSite.openObjι {X : B.Scheme} (V : (B.inclusion.obj X).Opens) :
    BigEtaleSite.openObj B V ⟶ X := ObjectProperty.homMk V.ι

/-- An open subscheme of an object `X` of the big étale site over `S`, as an object over `S`
through the inclusion into `X`. -/
public def BigEtaleOver.openObj {X : BigEtaleOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens) : BigEtaleOver B S.obj S.property :=
  Over.mk (BigEtaleSite.openObjι B V ≫ X.hom)

/-- The inclusion of an open subscheme of `X`, as a morphism of schemes over `S`. -/
public def BigEtaleOver.openObjι {X : BigEtaleOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens) : BigEtaleOver.openObj B S V ⟶ X :=
  Over.homMk (BigEtaleSite.openObjι B V) rfl

/-- On points, the inclusion of an open subscheme of `X` is the inclusion of that open. -/
public theorem BigEtaleOver.openObjι_apply {X : BigEtaleOver B S.obj S.property}
    (V : (B.inclusion.obj X.left).Opens) (y : B.inclusion.obj (BigEtaleOver.openObj B S V).left) :
    (B.inclusion.map (BigEtaleOver.openObjι B S V).left) y = V.ι y := rfl

/-- An open of `X` is contained in another as soon as every point of the first, viewed through
the inclusion of the corresponding object over `S`, lies in the second. -/
public theorem BigEtaleOver.le_of_forall_openObjι_mem {X : BigEtaleOver B S.obj S.property}
    (V W : (B.inclusion.obj X.left).Opens)
    (h : ∀ y, (B.inclusion.map (BigEtaleOver.openObjι B S V).left) y ∈ W) : V ≤ W :=
  fun _ hx => h ⟨_, hx⟩

/-- On points, the inclusion of an open subscheme of `Y` followed by `h : Y ⟶ X` is the
inclusion followed by `h`. -/
public theorem BigEtaleOver.openObjι_comp_apply {X Y : BigEtaleOver B S.obj S.property}
    (V : (B.inclusion.obj Y.left).Opens) (h : Y ⟶ X)
    (y : B.inclusion.obj (BigEtaleOver.openObj B S V).left) :
    (B.inclusion.map (BigEtaleOver.openObjι B S V ≫ h).left) y =
      (B.inclusion.map h.left) ((B.inclusion.map (BigEtaleOver.openObjι B S V).left) y) := by
  rw [← Scheme.Hom.comp_apply]
  rfl

/-- **The equality locus is compatible with restriction.** The equality locus of the
restrictions of two sections of `π_S⁻¹F` along `h : Y ⟶ X` is the inverse image of their
equality locus.

Both inclusions are obtained by testing the universal property against the inclusion of the
relevant open subscheme of `Y`, viewed as an object of the big étale site over `S`: the
equality locus of the restrictions identifies the two sections after restriction along that
inclusion, hence along its composite with `h`, and conversely. -/
public theorem etaleInverseImageEqLocus_preimage {X Y : BigEtaleOver B S.obj S.property}
    (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op X)) (h : Y ⟶ X) :
    B.inclusion.map h.left ⁻¹ᵁ etaleInverseImageEqLocus B S F X t₁ t₂ =
      etaleInverseImageEqLocus B S F Y ((etaleInverseImagePresheaf B S F).map h.op t₁)
        ((etaleInverseImagePresheaf B S F).map h.op t₂) := by
  refine le_antisymm (BigEtaleOver.le_of_forall_openObjι_mem B S _ _ ?_)
    (BigEtaleOver.le_of_forall_openObjι_mem B S _ _ ?_)
  · -- The inverse image of the equality locus lies in the equality locus of the restrictions.
    refine (forall_mem_etaleInverseImageEqLocus_iff B S F _ _
      (BigEtaleOver.openObjι B S (B.inclusion.map h.left ⁻¹ᵁ
        etaleInverseImageEqLocus B S F X t₁ t₂))).mpr ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
    refine (forall_mem_etaleInverseImageEqLocus_iff B S F t₁ t₂ _).mp fun y => ?_
    rw [BigEtaleOver.openObjι_comp_apply, BigEtaleOver.openObjι_apply]
    exact y.property
  · -- The equality locus of the restrictions lies in the inverse image of the equality locus.
    intro y
    rw [Scheme.Hom.mem_preimage, ← BigEtaleOver.openObjι_comp_apply]
    refine (forall_mem_etaleInverseImageEqLocus_iff B S F t₁ t₂ _).mpr ?_ y
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact (forall_mem_etaleInverseImageEqLocus_iff B S F _ _
      (BigEtaleOver.openObjι B S (etaleInverseImageEqLocus B S F Y
        ((etaleInverseImagePresheaf B S F).map h.op t₁)
        ((etaleInverseImagePresheaf B S F).map h.op t₂)))).mp fun z =>
      z.property

/-- **The equality locus is everything exactly when the two sections agree.** This is the
universal property at the identity of `X`. -/
public theorem etaleInverseImageEqLocus_eq_top_iff {X : BigEtaleOver B S.obj S.property}
    (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op X)) :
    etaleInverseImageEqLocus B S F X t₁ t₂ = ⊤ ↔ t₁ = t₂ := by
  constructor
  · intro hW
    simpa using (forall_mem_etaleInverseImageEqLocus_iff B S F t₁ t₂ (𝟙 X)).mp fun y => by
      rw [hW]
      trivial
  · rintro rfl
    exact TopologicalSpace.Opens.ext (Set.eq_univ_of_forall
      ((forall_mem_etaleInverseImageEqLocus_iff B S F t₁ t₁ (𝟙 X)).mpr rfl))

/-- **Geometric uniqueness on the big étale site.** Two sections of `π_S⁻¹F` over `Y` which
have the same restriction along every member of a family of morphisms that is jointly
surjective on points are equal.

By `AlgebraicGeometry.forall_mem_etaleInverseImageEqLocus_iff` the image of each member of
family lies in the equality locus of the two sections, so joint surjectivity makes the equality
locus all of `Y`. -/
public theorem eq_of_etaleInverseImage_map_eq_of_jointlySurjective
    {Y : BigEtaleOver B S.obj S.property} (t₁ t₂ : (etaleInverseImagePresheaf B S F).obj (op Y))
    {K : Type v} (W : K → BigEtaleOver B S.obj S.property) (g : ∀ k, W k ⟶ Y)
    (hsurj : ∀ y : B.inclusion.obj Y.left, ∃ k, y ∈ Set.range (B.inclusion.map (g k).left))
    (h : ∀ k, (etaleInverseImagePresheaf B S F).map (g k).op t₁ =
      (etaleInverseImagePresheaf B S F).map (g k).op t₂) :
    t₁ = t₂ := by
  refine (etaleInverseImageEqLocus_eq_top_iff B S F t₁ t₂).mp
    (TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_))
  obtain ⟨k, z, hz⟩ := hsurj y
  rw [← hz]
  exact (forall_mem_etaleInverseImageEqLocus_iff B S F t₁ t₂ (g k)).mpr (h k) z

/-! ### Descent of the equality loci along an fpqc covering -/

/-- The fibre product of two members of a family of schemes over `X`, as an object of the big
étale site over `S`. -/
public def BigEtaleOver.pairProduct {X : BigEtaleOver B S.obj S.property}
    {Y Z : BigEtaleOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigEtaleOver B S.obj S.property :=
  Over.mk (Limits.pullback.fst f.left g.left ≫ Y.hom)

/-- The first projection of the fibre product of two members of a family over `X`. -/
public def BigEtaleOver.pairProductFst {X : BigEtaleOver B S.obj S.property}
    {Y Z : BigEtaleOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigEtaleOver.pairProduct B S f g ⟶ Y :=
  Over.homMk (Limits.pullback.fst f.left g.left) rfl

/-- The second projection of the fibre product of two members of a family over `X`. -/
public def BigEtaleOver.pairProductSnd {X : BigEtaleOver B S.obj S.property}
    {Y Z : BigEtaleOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigEtaleOver.pairProduct B S f g ⟶ Z :=
  Over.homMk (Limits.pullback.snd f.left g.left) (by
    change Limits.pullback.snd f.left g.left ≫ Z.hom =
      Limits.pullback.fst f.left g.left ≫ Y.hom
    rw [← Over.w f, ← Over.w g, Limits.pullback.condition_assoc])

/-- The two projections of the fibre product agree over `X`. -/
public theorem BigEtaleOver.pairProduct_condition {X : BigEtaleOver B S.obj S.property}
    {Y Z : BigEtaleOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) :
    BigEtaleOver.pairProductFst B S f g ≫ f = BigEtaleOver.pairProductSnd B S f g ≫ g :=
  Over.OverMorphism.ext Limits.pullback.condition

/-- The morphism into the fibre product determined by a pair of morphisms agreeing over the
base. -/
private def BigEtaleOver.pairProductLift {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X)
    (g : Z ⟶ X) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    W ⟶ BigEtaleOver.pairProduct B S f g :=
  Over.homMk (Limits.pullback.lift a.left b.left (congrArg Over.Hom.left hab)) (by
    change Limits.pullback.lift a.left b.left (congrArg Over.Hom.left hab) ≫
      Limits.pullback.fst f.left g.left ≫ Y.hom = W.hom
    rw [Limits.pullback.lift_fst_assoc]
    exact Over.w a)

/-- The lift into the fibre product recovers its first component. -/
private theorem BigEtaleOver.pairProductLift_fst
    {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) (a : W ⟶ Y)
    (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    BigEtaleOver.pairProductLift B S f g a b hab ≫
      BigEtaleOver.pairProductFst B S f g = a :=
  Over.OverMorphism.ext (Limits.pullback.lift_fst _ _ _)

/-- The lift into the fibre product recovers its second component. -/
private theorem BigEtaleOver.pairProductLift_snd
    {X Y Z W : BigEtaleOver B S.obj S.property} (f : Y ⟶ X) (g : Z ⟶ X) (a : W ⟶ Y)
    (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    BigEtaleOver.pairProductLift B S f g a b hab ≫
      BigEtaleOver.pairProductSnd B S f g = b :=
  Over.OverMorphism.ext (Limits.pullback.lift_snd _ _ _)

/-- Two points of schemes of a big étale site with the same image in the base come from a common
point of the fibre product. -/
private theorem exists_point_pullback {X Y Z : B.Scheme} (f : Y ⟶ X) (g : Z ⟶ X)
    (y : B.inclusion.obj Y) (z : B.inclusion.obj Z)
    (h : B.inclusion.map f y = B.inclusion.map g z) :
    ∃ w : B.inclusion.obj (Limits.pullback f g),
      B.inclusion.map (Limits.pullback.fst f g) w = y ∧
        B.inclusion.map (Limits.pullback.snd f g) w = z := by
  obtain ⟨w, hy, hz⟩ := Scheme.Pullback.exists_preimage_pullback y z h
  refine ⟨(PreservesPullback.iso B.inclusion f g).inv w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst]
    exact hy
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_snd]
    exact hz

/-- A jointly surjective family stays jointly surjective after base change: first projections
version. -/
private theorem BigEtaleOver.exists_mem_range_pairProductFst
    {X W : BigEtaleOver B S.obj S.property}
    (q : W ⟶ X) {K : Type v} (V : K → BigEtaleOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
    (hsurj : ∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left))
    (w : B.inclusion.obj W.left) :
    ∃ k, w ∈ Set.range (B.inclusion.map (BigEtaleOver.pairProductFst B S q (v k)).left) := by
  obtain ⟨k, z, hz⟩ := hsurj ((B.inclusion.map q.left) w)
  obtain ⟨y, hy, -⟩ := exists_point_pullback B q.left (v k).left w z hz.symm
  exact ⟨k, y, hy⟩

/-- A jointly surjective family stays jointly surjective after base change: second projections
version. -/
private theorem BigEtaleOver.exists_mem_range_pairProductSnd
    {X Z : BigEtaleOver B S.obj S.property}
    (r : Z ⟶ X) {K : Type v} (V : K → BigEtaleOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
    (hsurj : ∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left))
    (z : B.inclusion.obj Z.left) :
    ∃ k, z ∈ Set.range (B.inclusion.map (BigEtaleOver.pairProductSnd B S (v k) r).left) := by
  obtain ⟨k, y, hy⟩ := hsurj ((B.inclusion.map r.left) z)
  obtain ⟨w, -, hw⟩ := exists_point_pullback B (v k).left r.left y z hy
  exact ⟨k, w, hw⟩

/-- **Stacks 09XN, step 4: the equality loci of a compatible family descend.** Let
`{p i : Z i ⟶ X}` be a family of schemes over `S` whose underlying family of morphisms of
schemes is an fpqc covering of `X`, let `x i` be a compatible family of sections of `π_S⁻¹F`
over the `Z i`, and let `t` be a section of `π_S⁻¹F` over `X`. Then the open loci on which
`x i` agrees with the restriction of `t` come from a unique open of `X`.

The loci pull back to the same open on each fibre product `Z i ×_X Z j`: by
`AlgebraicGeometry.etaleInverseImageEqLocus_preimage` the two inverse images are the equality loci
of the restricted sections, the restrictions of `x i` and `x j` agree there by compatibility,
and the restrictions of `t` agree there because the two projections agree over `X`. Stacks 03N0
then descends them. -/
public theorem existsUnique_preimage_eq_etaleInverseImageEqLocus
    {X : BigEtaleOver B S.obj S.property} {I : Type v}
    (Z : I → BigEtaleOver B S.obj S.property) (p : ∀ i, Z i ⟶ X)
    (hp : Presieve.ofArrows Z p ∈
      Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X)
    (x : ∀ i, (etaleInverseImagePresheaf B S F).obj (op (Z i)))
    (hx : Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F) p x)
    (t : (etaleInverseImagePresheaf B S F).obj (op X)) :
    ∃! V : (B.inclusion.obj X.left).Opens, ∀ i,
      B.inclusion.map (p i).left ⁻¹ᵁ V =
        etaleInverseImageEqLocus B S F (Z i) (x i)
          ((etaleInverseImagePresheaf B S F).map (p i).op t) := by
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hp
  refine existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage
    (fun i => B.inclusion.obj (Z i).left) (fun i => B.inclusion.map (p i).left) hp
    (fun i => etaleInverseImageEqLocus B S F (Z i) (x i)
      ((etaleInverseImagePresheaf B S F).map (p i).op t)) fun i j => ?_
  have hcond := BigEtaleOver.pairProduct_condition B S (p i) (p j)
  have hkey : B.inclusion.map (Limits.pullback.fst (p i).left (p j).left) ⁻¹ᵁ
        etaleInverseImageEqLocus B S F (Z i) (x i)
          ((etaleInverseImagePresheaf B S F).map (p i).op t) =
      B.inclusion.map (Limits.pullback.snd (p i).left (p j).left) ⁻¹ᵁ
        etaleInverseImageEqLocus B S F (Z j) (x j)
          ((etaleInverseImagePresheaf B S F).map (p j).op t) := by
    have h1 := etaleInverseImageEqLocus_preimage B S F (x i)
      ((etaleInverseImagePresheaf B S F).map (p i).op t)
      (BigEtaleOver.pairProductFst B S (p i) (p j))
    have h2 := etaleInverseImageEqLocus_preimage B S F (x j)
      ((etaleInverseImagePresheaf B S F).map (p j).op t)
      (BigEtaleOver.pairProductSnd B S (p i) (p j))
    rw [hx i j (BigEtaleOver.pairProduct B S (p i) (p j))
      (BigEtaleOver.pairProductFst B S (p i) (p j))
      (BigEtaleOver.pairProductSnd B S (p i) (p j)) hcond, ← Functor.map_comp_apply, ← op_comp,
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
private theorem etaleInverseImage_map_eq_of_agree_on_pairProduct
    {X V Z W : BigEtaleOver B S.obj S.property}
    (f : V ⟶ X) (g : Z ⟶ X) (tV : (etaleInverseImagePresheaf B S F).obj (op V))
    (tZ : (etaleInverseImagePresheaf B S F).obj (op Z))
    (hagree : (etaleInverseImagePresheaf B S F).map (BigEtaleOver.pairProductFst B S f g).op tV =
      (etaleInverseImagePresheaf B S F).map (BigEtaleOver.pairProductSnd B S f g).op tZ)
    (a : W ⟶ V) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g) :
    (etaleInverseImagePresheaf B S F).map a.op tV =
      (etaleInverseImagePresheaf B S F).map b.op tZ := by
  rw [← BigEtaleOver.pairProductLift_fst B S f g a b hab, op_comp, Functor.map_comp_apply,
    hagree, ← Functor.map_comp_apply, ← op_comp, BigEtaleOver.pairProductLift_snd]

/-- The presheaf underlying `π_S⁻¹F` is a sheaf for the big étale topology. -/
public theorem etaleInverseImagePresheaf_isSheaf :
    Presieve.IsSheaf (BigEtaleOver.topology B S.obj S.property)
      (etaleInverseImagePresheaf B S F) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).property

/-- **Stacks 09XN, steps 4 and 5: the existence half from local representability.** Suppose
that every compatible family of sections of `π_S⁻¹F` on an fpqc covering of an object `X` of
the big étale site over `S` is *locally represented*: there is a family `{v k : V k ⟶ X}` which
generates a covering sieve of the big étale topology and is jointly surjective on points,
together with sections `t k` of `π_S⁻¹F` over `V k`, such that `t k` agrees with every member
of the family on the fibre products `V k ×_X Z i`. Then every compatible family of sections of
`π_S⁻¹F` on an fpqc covering has an amalgamation.

The sections `t k` form a compatible family for `{v k}`: any two of them agree after being
pulled back to a common object `W` over `X`, because they both agree there with every member
of the original family, and the base changes of the original fpqc covering to `W` are jointly
surjective, so geometric uniqueness applies. Since `π_S⁻¹F` is a sheaf for the big étale
topology the `t k` glue to a section `t` over `X`, and the same geometric uniqueness argument
— now along the base changes of `{v k}` — identifies the restriction of `t` with each member
of the family. -/
public theorem exists_isAmalgamation_of_locallyRepresentable
    (hrep : ∀ (X : BigEtaleOver B S.obj S.property) (I : Type (u + 1))
      (Z : I → BigEtaleOver B S.obj S.property) (p : ∀ i, Z i ⟶ X),
      Presieve.ofArrows Z p ∈
        Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X →
      ∀ x : ∀ i, (etaleInverseImagePresheaf B S F).obj (op (Z i)),
      Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F) p x →
      ∃ (K : Type (u + 1)) (V : K → BigEtaleOver B S.obj S.property) (v : ∀ k, V k ⟶ X)
        (t : ∀ k, (etaleInverseImagePresheaf B S F).obj (op (V k))),
        Sieve.generate (Presieve.ofArrows V v) ∈
            BigEtaleOver.topology B S.obj S.property X ∧
          (∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left)) ∧
          ∀ k i, (etaleInverseImagePresheaf B S F).map
                (BigEtaleOver.pairProductFst B S (v k) (p i)).op (t k) =
            (etaleInverseImagePresheaf B S F).map
              (BigEtaleOver.pairProductSnd B S (v k) (p i)).op (x i))
    {X : BigEtaleOver B S.obj S.property} (R : Presieve X)
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S.obj S.property) X)
    (y : Presieve.FamilyOfElements (etaleInverseImagePresheaf B S F) R) (hy : y.Compatible) :
    ∃ t, y.IsAmalgamation t := by
  obtain ⟨I, Z, p, rfl⟩ := R.exists_eq_ofArrows
  have hxA : Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F) p
      (fun i => y (p i) (Presieve.ofArrows.mk i)) :=
    fun i j W gi gj hg => hy gi gj (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) hg
  obtain ⟨K, V, v, t, hsieve, hsurjV, hagree⟩ := hrep X I Z p hR _ hxA
  have hsurjZ : ∀ z : B.inclusion.obj X.left,
      ∃ i, z ∈ Set.range (B.inclusion.map (p i).left) := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
    exact fpqc_jointly_surjective _ hR
  -- The local sections form a compatible family for the refined covering.
  have htA : Presieve.Arrows.Compatible (etaleInverseImagePresheaf B S F) v t := by
    intro k l W g₁ g₂ hg
    refine eq_of_etaleInverseImage_map_eq_of_jointlySurjective B S F _ _
      (fun i => BigEtaleOver.pairProduct B S (g₁ ≫ v k) (p i))
      (fun i => BigEtaleOver.pairProductFst B S (g₁ ≫ v k) (p i))
      (BigEtaleOver.exists_mem_range_pairProductFst B S (g₁ ≫ v k) Z p hsurjZ) fun i => ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hcond := BigEtaleOver.pairProduct_condition B S (g₁ ≫ v k) (p i)
    exact (etaleInverseImage_map_eq_of_agree_on_pairProduct B S F (v k) (p i) (t k) _
      (hagree k i) _ _
      ((Category.assoc _ _ _).trans hcond)).trans
      (etaleInverseImage_map_eq_of_agree_on_pairProduct B S F (v l) (p i) (t l) _
      (hagree l i) _ _
      ((Category.assoc _ _ _).trans ((_ ≫= hg.symm).trans hcond))).symm
  -- The refined covering is a covering of the big étale topology, so the sections glue.
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff
    (P := etaleInverseImagePresheaf B S F) (π := v)).mp
    ((Presieve.isSheafFor_iff_generate _).mpr
      (etaleInverseImagePresheaf_isSheaf B S F _ hsieve)) t htA
  -- The glued section restricts to the given family.
  refine ⟨s, ?_⟩
  rw [Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows]
  intro i
  refine eq_of_etaleInverseImage_map_eq_of_jointlySurjective B S F _ _
    (fun k => BigEtaleOver.pairProduct B S (v k) (p i))
    (fun k => BigEtaleOver.pairProductSnd B S (v k) (p i))
    (BigEtaleOver.exists_mem_range_pairProductSnd B S (p i) V v hsurjV) fun k => ?_
  rw [← Functor.map_comp_apply, ← op_comp,
    ← BigEtaleOver.pairProduct_condition B S (v k) (p i), op_comp,
    Functor.map_comp_apply, hs k]
  exact hagree k i

end Relative

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09XN, the fpqc sheaf condition from local representability.** The presheaf
`X ↦ Γ(X_ét, f_X⁻¹F)` on the big étale site over `S` — the underlying presheaf of `π_S⁻¹F` — is
a sheaf for the fpqc topology as soon as every compatible family of its sections on an fpqc
covering is locally represented by sections over a big-étale covering of the base, in the sense
of `AlgebraicGeometry.exists_isAmalgamation_of_locallyRepresentable`.

The uniqueness half is
`AlgebraicGeometry.bigEtaleToSmallEtale_inverseImage_isSeparatedFor_fpqc`, which is
unconditional; local representability is the only remaining input, and it is the step in the
proof of Stacks 09XN which produces, after an étale refinement of the covering, an object of
the small étale site of `X` and a section of `F` over it representing a given local section. -/
public theorem bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_locallyRepresentable
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (hrep : ∀ (X : BigEtaleOver B S hS) (I : Type (u + 1))
      (Z : I → BigEtaleOver B S hS) (p : ∀ i, Z i ⟶ X),
      Presieve.ofArrows Z p ∈
        Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS) X →
      ∀ x : ∀ i, (etaleInverseImagePresheaf B (B.obj S hS) F).obj (op (Z i)),
      Presieve.Arrows.Compatible (etaleInverseImagePresheaf B (B.obj S hS) F) p x →
      ∃ (K : Type (u + 1)) (V : K → BigEtaleOver B S hS) (v : ∀ k, V k ⟶ X)
        (t : ∀ k, (etaleInverseImagePresheaf B (B.obj S hS) F).obj (op (V k))),
        Sieve.generate (Presieve.ofArrows V v) ∈ BigEtaleOver.topology B S hS X ∧
          (∀ y : B.inclusion.obj X.left, ∃ k, y ∈ Set.range (B.inclusion.map (v k).left)) ∧
          ∀ k i, (etaleInverseImagePresheaf B (B.obj S hS) F).map
                (BigEtaleOver.pairProductFst B (B.obj S hS) (v k) (p i)).op (t k) =
            (etaleInverseImagePresheaf B (B.obj S hS) F).map
              (BigEtaleOver.pairProductSnd B (B.obj S hS) (v k) (p i)).op (x i)) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigEtaleOver.toScheme B S hS)).toGrothendieck)
      ((bigEtaleToSmallEtaleMorphism B S hS).inverseImage.obj F).obj :=
  bigEtaleToSmallEtale_inverseImage_isSheaf_fpqc_of_exists_isAmalgamation B S hS F
    fun {_X} R hR x hx =>
      exists_isAmalgamation_of_locallyRepresentable B (B.obj S hS) F hrep R hR x hx

end AlgebraicGeometry
