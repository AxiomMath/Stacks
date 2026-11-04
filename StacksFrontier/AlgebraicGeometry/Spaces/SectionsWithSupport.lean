module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf

/-!
# Sections with support in a closed subspace

Let `X` be an algebraic space over a scheme `S` and let `F` be an abelian sheaf on the small
étale site of `X`. For a subset `T` of the points of `X`, the sections of `F` over an étale
chart whose support maps into `T` form an abelian subsheaf of `F`: the condition is a subgroup
condition over each chart, it is stable under restriction, and it is local on covering sieves.
For `T` the point set of a closed immersion `i : Z ⟶ X` this subsheaf is the sheaf
`H_Z(F)` of Stacks 0A4L, and pushing it to the small étale site of `Z` along the inverse image
gives the functor `H_Z` from abelian sheaves on `X_étale` to abelian sheaves on `Z_étale`.

## Main definitions

* `AlgebraicGeometry.Space.SectionSupportedOn`: the condition on a section of an abelian sheaf
  over an étale chart that its support maps into a prescribed set of points.
* `AlgebraicGeometry.Space.sectionsWithSupportSheaf`: the abelian subsheaf of sections
  satisfying that condition, with `AlgebraicGeometry.Space.sectionsWithSupportSheafInclusion`
  its inclusion into the ambient sheaf.
* `AlgebraicGeometry.Space.sectionsWithSupport`: the same construction as an endofunctor of the
  category of abelian sheaves on the small étale site, with
  `AlgebraicGeometry.Space.sectionsWithSupportInclusion` the inclusion into the identity
  functor.
* `AlgebraicGeometry.Space.sectionsWithSupportInClosedSubspace`: the functor `H_Z` of
  Stacks 0A4L for a closed immersion `i : Z ⟶ X`, from abelian sheaves on the small étale site
  of `X` to abelian sheaves on the small étale site of `Z`.

## Main results

* `AlgebraicGeometry.Space.mem_sectionsWithSupportSheaf_iff`: a section of `F` over an étale
  chart is a section of the subsheaf exactly when its support maps into `T`. This is the
  sectionwise characterization that pins the construction to the source's definition.
* `AlgebraicGeometry.Space.sectionSupportedOn_of_sieve`: the support condition is local on
  covering sieves, which is what makes the construction a subsheaf.
* `AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`: a section with empty support
  is zero.
* `AlgebraicGeometry.Space.sectionsWithSupportSheafInclusion_mono` and
  `AlgebraicGeometry.Space.sectionsWithSupport_additive`: the inclusion is a monomorphism and
  the functor is additive.

## Implementation notes

The subsheaf is built as in
`StacksFrontier/AlgebraicGeometry/Spaces/SupportedSectionsSubsheaf.lean`, where the same
construction is carried out for sheaves of modules: the four closure properties of the support
recorded with Stacks 04KA give the subgroup over each chart and its stability under
restriction, and locality is joint surjectivity of a covering sieve on points,
`AlgebraicGeometry.Space.SmallEtale.exists_mem_arrows_pointsMap_eq`. The sheaf condition is
then checked on the underlying sets through `CategoryTheory.Subfunctor.isSheaf_iff`, and
transported back to abelian groups by `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`.

The subsheaf on `X_étale` is stated for an arbitrary set `T` of points of an arbitrary presheaf
on the big fppf site, and with the coefficient universe free: no sheafification is involved, so
nothing forces the universe of the abelian groups. The functor `H_Z` to `Z_étale` is a different
matter. Its second factor is the inverse image along `i`, which exists only where the small
étale site has sheafification for abelian groups, and the universe chosen here is `u + 1`, the
universe in which the objects of the site live. There `AlgebraicGeometry.Space.SmallEtale`
carries `HasSheafify` as an instance, so the inverse image is the honest functor
`CategoryTheory.Functor.sheafPullback` rather than a left adjoint extracted from an existence
statement; it is also the universe of the two results about a closed immersion that consumers of
this file use, the left-inverse clause of Stacks 04E5, part (2) and the exactness of the inverse
image of Stacks 04K2. At the wider universe `max (u + 1) v` of
`AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint_abelian` the inverse image is only
available as `Classical.choice` of a `Nonempty`, which is why that universe is not used.

Only the subsheaf construction carries a tag. Stacks 0A4L also introduces the sections with
support `Γ_Z(X, -)`, its right derived functor, the higher cohomology with support, the derived
functor `R H_Z` and the spectral sequence relating them; none of those is defined here, so the
tag is carried with a note naming the single entity that is.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Subsheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Sections with support in a subset of the points -/

/-- A section of an abelian sheaf on the small étale site over an étale chart is *supported
on* a set `T` of points of the ambient presheaf when its support maps into `T`. -/
def SectionSupportedOn (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) : Prop :=
  supportOfSection B S hS X F U σ ⊆ pointsMap B S hS _ U.obj.hom ⁻¹' T

variable {B S hS X} {T : Set (points B S hS X)}
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}}

/-- The zero section is supported on every set of points: its support is empty. -/
theorem sectionSupportedOn_zero (U : SmallEtale B S hS X) :
    SectionSupportedOn B S hS X T F U 0 :=
  (supportOfSection_zero B S hS X F U).le.trans (Set.empty_subset _)

/-- Sections supported on a set of points are closed under addition. -/
theorem sectionSupportedOn_add {U : SmallEtale B S hS X} {σ τ : F.obj.obj (op U)}
    (hσ : SectionSupportedOn B S hS X T F U σ) (hτ : SectionSupportedOn B S hS X T F U τ) :
    SectionSupportedOn B S hS X T F U (σ + τ) := by
  intro x hx
  rcases supportOfSection_add_subset B S hS X F U σ τ hx with h | h
  · exact hσ h
  · exact hτ h

/-- Sections supported on a set of points are closed under negation. -/
theorem sectionSupportedOn_neg {U : SmallEtale B S hS X} {σ : F.obj.obj (op U)}
    (hσ : SectionSupportedOn B S hS X T F U σ) :
    SectionSupportedOn B S hS X T F U (-σ) := by
  intro x hx
  exact hσ ((supportOfSection_neg B S hS X F U σ).le hx)

/-- A point of a chart over `U` lies over `T` exactly when its image in `U` does. -/
private theorem pointsMap_hom_mem_iff {U V : SmallEtale B S hS X} (g : V ⟶ U)
    (y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V))) :
    pointsMap B S hS _ V.obj.hom y ∈ T ↔
      pointsMap B S hS _ U.obj.hom
        (pointsMap B S hS _ (yoneda.map ((SmallEtale.toOver B S hS X).map g)) y) ∈ T :=
  (congrArg (· ∈ T) (pointsMap_chart_hom B S hS X g y)).symm.to_iff

/-- Sections supported on a set of points are stable under restriction to a chart over the
given one: the support of a restriction is the preimage of the support. -/
theorem sectionSupportedOn_restrict {U V : SmallEtale B S hS X} (g : V ⟶ U)
    (σ : F.obj.obj (op U)) (hσ : SectionSupportedOn B S hS X T F U σ) :
    SectionSupportedOn B S hS X T F V (F.obj.map g.op σ) := fun y hy ↦
  (pointsMap_hom_mem_iff g y).2 (hσ ((supportOfSection_restrict B S hS X F U σ V g).le hy))

/-- A morphism of abelian sheaves carries sections supported on a set of points to sections
supported on that set: it cannot enlarge the support of a section. -/
theorem sectionSupportedOn_map (φ : F ⟶ G) {U : SmallEtale B S hS X} (σ : F.obj.obj (op U))
    (hσ : SectionSupportedOn B S hS X T F U σ) :
    SectionSupportedOn B S hS X T G U (φ.hom.app (op U) σ) :=
  fun _ hx ↦ hσ (supportOfSection_map_subset B S hS X φ U σ hx)

/-- Being supported on a set of points is local on covering sieves: a section whose
restriction to every member of a covering sieve is supported on `T` is itself supported
on `T`.

This is the locality that makes the sections supported on `T` a sub*sheaf*; it is joint
surjectivity of a covering sieve on points,
`AlgebraicGeometry.Space.SmallEtale.exists_mem_arrows_pointsMap_eq`, together with the
identification of the support of a restriction with the preimage of the support. -/
theorem sectionSupportedOn_of_sieve {U : SmallEtale B S hS X} (σ : F.obj.obj (op U))
    {R : Sieve U} (hR : R ∈ SmallEtale.topology B S hS X U)
    (h : ∀ ⦃V : SmallEtale B S hS X⦄ (f : V ⟶ U), R.arrows f →
      SectionSupportedOn B S hS X T F V (F.obj.map f.op σ)) :
    SectionSupportedOn B S hS X T F U σ := by
  intro x hx
  obtain ⟨V, f, hf, y, hy⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS X hR x
  refine hy ▸ (pointsMap_hom_mem_iff f y).1 (h f hf ?_)
  rw [supportOfSection_restrict B S hS X F U σ V f, Set.mem_preimage, hy]
  exact hx

/-- A section with empty support is zero: its largest open zero locus is the whole chart, so
the restriction criterion applies to the identity. -/
theorem eq_zero_of_supportOfSection_eq_empty (U : SmallEtale B S hS X)
    (σ : F.obj.obj (op U)) (hσ : supportOfSection B S hS X F U σ = ∅) : σ = 0 := by
  have htop : ∀ y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)),
      y ∈ (largestOpenZeroLocus B S hS X F U σ).1 := by
    intro y
    by_contra hy
    exact (Set.eq_empty_iff_forall_notMem.1 hσ y) hy
  have h := (largestOpenZeroLocus_restrict_iff B S hS X F U σ U (𝟙 U)).2 fun y ↦ htop _
  rw [op_id, F.obj.map_id] at h
  exact h

/-- A section over a chart with no points is zero. -/
theorem eq_zero_of_isEmpty_points (U : SmallEtale B S hS X)
    (hU : IsEmpty (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U))))
    (σ : F.obj.obj (op U)) : σ = 0 :=
  eq_zero_of_supportOfSection_eq_empty U σ
    (Set.eq_empty_iff_forall_notMem.2 fun x _ ↦ hU.elim x)

/-! ### The subsheaf of sections with support -/

variable (B S hS X)

/-- The sections of an abelian sheaf over an étale chart which are supported on `T`, as an
additive subgroup. -/
def sectionsWithSupportSubgroup (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) : AddSubgroup (F.obj.obj (op U)) where
  carrier := {σ | SectionSupportedOn B S hS X T F U σ}
  add_mem' := sectionSupportedOn_add
  zero_mem' := sectionSupportedOn_zero U
  neg_mem' := sectionSupportedOn_neg

/-- The support condition as a subfunctor of the underlying sets of the sheaf. -/
def sectionsWithSupportSubfunctor (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Subfunctor (F.obj ⋙ forget AddCommGrpCat.{v}) where
  obj U := {σ | SectionSupportedOn B S hS X T F U.unop σ}
  map {_ _} g σ hσ := sectionSupportedOn_restrict g.unop σ hσ

/-- The underlying sets of an abelian sheaf form a sheaf of types. -/
theorem forget_isSheaf (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Presieve.IsSheaf (SmallEtale.topology B S hS X) (F.obj ⋙ forget AddCommGrpCat.{v}) :=
  (isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS X)
      (F.obj ⋙ forget AddCommGrpCat.{v})).mp
    (Presheaf.isSheaf_comp_of_isSheaf (SmallEtale.topology B S hS X) F.obj
      (forget AddCommGrpCat.{v}) F.property)

/-- The support condition cuts out a sheaf of types, by its locality on covering sieves. -/
theorem sectionsWithSupportSubfunctor_isSheaf (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Presieve.IsSheaf (SmallEtale.topology B S hS X)
      (sectionsWithSupportSubfunctor B S hS X T F).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (forget_isSheaf B S hS X F)]
  intro U σ hσ
  exact sectionSupportedOn_of_sieve σ hσ fun _ _ hf ↦ hf

/-- The presheaf of sections supported on `T`. -/
def sectionsWithSupportPresheaf (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    (SmallEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj U := AddCommGrpCat.of (sectionsWithSupportSubgroup B S hS X T F U.unop)
  map {U V} g := AddCommGrpCat.ofHom
    { toFun := fun σ ↦ ⟨F.obj.map g σ.1, sectionSupportedOn_restrict g.unop σ.1 σ.2⟩
      map_zero' := by ext; exact map_zero _
      map_add' := fun σ τ ↦ by ext; exact map_add _ _ _ }
  map_id U := by
    ext σ
    change (F.obj.map (𝟙 U)) σ.1 = σ.1
    exact congrArg (fun k ↦ k σ.1) (F.obj.map_id U)
  map_comp {U V W} g h := by
    ext σ
    change (F.obj.map (g ≫ h)) σ.1 = (F.obj.map h) ((F.obj.map g) σ.1)
    exact congrArg (fun k ↦ k σ.1) (F.obj.map_comp g h)

/-- The inclusion of the presheaf of sections supported on `T` into the ambient sheaf. -/
def sectionsWithSupportPresheafInclusion (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    sectionsWithSupportPresheaf B S hS X T F ⟶ F.obj where
  app U := AddCommGrpCat.ofHom (sectionsWithSupportSubgroup B S hS X T F U.unop).subtype
  naturality {U V} g := by ext σ; rfl

/-- The underlying sets of the presheaf of sections supported on `T` are the subfunctor cut
out by the support condition. -/
def sectionsWithSupportUnderlyingIso (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    sectionsWithSupportPresheaf B S hS X T F ⋙ forget AddCommGrpCat.{v} ≅
      (sectionsWithSupportSubfunctor B S hS X T F).toFunctor :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso
      { toFun := fun σ ↦ ⟨σ.1, σ.2⟩
        invFun := fun σ ↦ ⟨σ.1, σ.2⟩
        left_inv := fun _ ↦ Subtype.ext rfl
        right_inv := fun _ ↦ Subtype.ext rfl })
    fun _ ↦ by ext σ; rfl

/-- **Stacks 0A4L.** The abelian subsheaf of sections supported on a set `T` of points: over
an étale chart it consists of the sections of `F` whose support maps into `T`.

For `T` the point set of a closed immersion `i : Z ⟶ X` this is the sheaf `H_Z(F)` of the
source, before it is viewed on the small étale site of `Z`. -/
@[stacks 0A4L "the subsheaf of sections with support in a closed subspace"]
def sectionsWithSupportSheaf (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v} :=
  ⟨sectionsWithSupportPresheaf B S hS X T F,
    Presheaf.isSheaf_of_isSheaf_comp (SmallEtale.topology B S hS X)
      (sectionsWithSupportPresheaf B S hS X T F) (forget AddCommGrpCat.{v})
      ((Presheaf.isSheaf_of_iso_iff (sectionsWithSupportUnderlyingIso B S hS X T F)).2
        ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS X)
          (sectionsWithSupportSubfunctor B S hS X T F).toFunctor).mpr
          (sectionsWithSupportSubfunctor_isSheaf B S hS X T F)))⟩

/-- A section of `F` over an étale chart is a section of the subsheaf of sections supported
on `T` exactly when its support maps into `T`.

This is the sectionwise characterization of
`AlgebraicGeometry.Space.sectionsWithSupportSheaf`: it is the source's definition of
`H_Z(F)`. -/
theorem mem_sectionsWithSupportSheaf_iff (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) (U : SmallEtale B S hS X)
    (σ : F.obj.obj (op U)) :
    σ ∈ sectionsWithSupportSubgroup B S hS X T F U ↔ SectionSupportedOn B S hS X T F U σ :=
  Iff.rfl

/-- The inclusion of the subsheaf of sections supported on `T` into the ambient sheaf. -/
def sectionsWithSupportSheafInclusion (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    sectionsWithSupportSheaf B S hS X T F ⟶ F :=
  ⟨sectionsWithSupportPresheafInclusion B S hS X T F⟩

/-- The inclusion of the subsheaf of sections supported on `T` is a monomorphism. -/
instance sectionsWithSupportSheafInclusion_mono (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Mono (sectionsWithSupportSheafInclusion B S hS X T F) :=
  have : Mono (sectionsWithSupportSheafInclusion B S hS X T F).hom := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    exact (AddCommGrpCat.mono_iff_injective _).mpr fun _ _ h ↦ Subtype.ext h
  Sheaf.Hom.mono_of_presheaf_mono (SmallEtale.topology B S hS X) AddCommGrpCat.{v}
    (sectionsWithSupportSheafInclusion B S hS X T F)

/-- The support of a section of the subsheaf of sections with support is contained in its
support in the ambient sheaf.

The inclusion is injective on sections, so a restriction killing the section in the ambient
sheaf kills it in the subsheaf; maximality of the largest open zero locus then applies. -/
theorem supportOfSection_sectionsWithSupportSheaf_subset (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) (U : SmallEtale B S hS X)
    (σ : (sectionsWithSupportSheaf B S hS X T F).obj.obj (op U)) :
    supportOfSection B S hS X (sectionsWithSupportSheaf B S hS X T F) U σ ⊆
      supportOfSection B S hS X F U σ.1 :=
  Set.compl_subset_compl.2 <|
    largestOpenZeroLocus_maximal B S hS X (sectionsWithSupportSheaf B S hS X T F) U σ _
      fun V f hf ↦ Subtype.ext
        ((largestOpenZeroLocus_restrict_iff B S hS X F U σ.1 V f).2 hf)

/-- Every section of the subsheaf of sections with support on `T` is, as a section of that
subsheaf, again supported on `T`. -/
theorem sectionSupportedOn_sectionsWithSupportSheaf (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) (U : SmallEtale B S hS X)
    (σ : (sectionsWithSupportSheaf B S hS X T F).obj.obj (op U)) :
    SectionSupportedOn B S hS X T (sectionsWithSupportSheaf B S hS X T F) U σ :=
  fun _ hx ↦ σ.2 (supportOfSection_sectionsWithSupportSheaf_subset B S hS X T F U σ hx)

/-! ### Sections with support as a functor -/

/-- The morphism of subsheaves of sections supported on `T` induced by a morphism of abelian
sheaves. -/
def sectionsWithSupportMap (T : Set (points B S hS X))
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}} (φ : F ⟶ G) :
    sectionsWithSupportSheaf B S hS X T F ⟶ sectionsWithSupportSheaf B S hS X T G :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
       { toFun := fun σ ↦ ⟨φ.hom.app U σ.1, sectionSupportedOn_map φ σ.1 σ.2⟩
         map_zero' := by ext; exact map_zero _
         map_add' := fun σ τ ↦ by ext; exact map_add _ _ _ }
     naturality := fun {U V} g ↦ by
       ext σ
       refine Subtype.ext ?_
       exact congrArg (fun k ↦ (ConcreteCategory.hom k) σ.1) (φ.hom.naturality g) }⟩

/-- **Stacks 0A4L.** Sections with support on a fixed set of points, as an endofunctor of the
abelian sheaves on the small étale site of `X`. -/
@[stacks 0A4L "sections with support in a closed subspace, functorially"]
def sectionsWithSupport (T : Set (points B S hS X)) :
    Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v} where
  obj F := sectionsWithSupportSheaf B S hS X T F
  map φ := sectionsWithSupportMap B S hS X T φ
  map_id F := by
    refine Sheaf.hom_ext ?_
    ext U σ
    rfl
  map_comp φ ψ := by
    refine Sheaf.hom_ext ?_
    ext U σ
    rfl

/-- The inclusion of the sections with support on `T` into the ambient sheaf, as a morphism of
functors. -/
def sectionsWithSupportInclusion (T : Set (points B S hS X)) :
    sectionsWithSupport.{v} B S hS X T ⟶
      𝟭 (Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) where
  app F := sectionsWithSupportSheafInclusion B S hS X T F
  naturality F G φ := by
    refine Sheaf.hom_ext ?_
    ext U σ
    rfl

/-- Each component of the inclusion of the sections with support is a monomorphism. -/
instance sectionsWithSupportInclusion_app_mono (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    Mono ((sectionsWithSupportInclusion.{v} B S hS X T).app F) :=
  sectionsWithSupportSheafInclusion_mono B S hS X T F

/-- Sections with support on a fixed set of points is an additive functor. -/
instance sectionsWithSupport_additive (T : Set (points B S hS X)) :
    (sectionsWithSupport.{v} B S hS X T).Additive where
  map_add {F G φ ψ} := by
    refine Sheaf.hom_ext ?_
    ext U σ
    rfl

end Subsheaf

/-! ### The functor `H_Z` of a closed immersion -/

section ClosedImmersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- The direct image of abelian sheaves along a morphism of algebraic spaces with representable
underlying morphism: restriction along base change of étale scheme charts. -/
abbrev smallEtaleAbelianPushforward (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v} :=
  letI := (smallBaseChange_isMorphismOfSites B S hS i hr).toIsContinuous
  (smallBaseChange B S hS i hr).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)

/-- The direct image of abelian sheaves on small étale sites is additive: it is restriction
along a functor, so it is computed on sections. -/
instance smallEtaleAbelianPushforward_additive (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    (smallEtaleAbelianPushforward.{v} B S hS i hr).Additive where
  map_add := by
    refine Sheaf.hom_ext ?_
    ext U x
    rfl

/-- The sections with support in the point set of a closed immersion `i : Z ⟶ X`: the sheaf
`H_Z(F)` of Stacks 0A4L, as a subsheaf of `F` on the small étale site of `X`. -/
abbrev closedSectionsWithSupport (i : Z ⟶ X) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v} :=
  sectionsWithSupport.{v} B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))

/-- **Every section of a direct image along a closed immersion `i : Z ⟶ X` has support in the
point set of `i`.**

This is the observation on which the source's description of the sections with support rests.
A point of the chart outside the point set of `i` has, the latter being closed by Stacks 04CD,
an open neighbourhood in the chart which misses it; the base change of that neighbourhood along
`i` has no points, so every section of the sheaf on `Z_étale` over it vanishes, and the point is
therefore in the largest open zero locus of the section. -/
theorem sectionSupportedOn_smallEtaleAbelianPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X.1)
    (σ : ((smallEtaleAbelianPushforward.{v} B S hS i hi.rep).obj G).obj.obj (op U)) :
    SectionSupportedOn B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))
      ((smallEtaleAbelianPushforward.{v} B S hS i hi.rep).obj G) U σ := by
  have hTclosed : IsClosed (Set.range (pointsMap B S hS Z.1 i.hom)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS X.property i.hom hi
  -- The complement of the preimage of `|Z|` is an open on which `σ` vanishes.
  have hopen : IsOpen (pointsMap B S hS _ U.obj.hom ⁻¹'
      (Set.range (pointsMap B S hS Z.1 i.hom))ᶜ) :=
    (continuous_pointsMap B S hS U.obj.hom).isOpen_preimage _ hTclosed.isOpen_compl
  have hmax := largestOpenZeroLocus_maximal B S hS X.1
    ((smallEtaleAbelianPushforward.{v} B S hS i hi.rep).obj G) U σ ⟨_, hopen⟩ ?_
  · intro x hx
    by_contra hnot
    exact hx (hmax hnot)
  -- A chart of `X` whose points all miss `|Z|` base-changes to a chart of `Z` with no points.
  intro V f hf
  have hVT : ∀ y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)),
      pointsMap B S hS _ V.obj.hom y ∉ Set.range (pointsMap B S hS Z.1 i.hom) :=
    fun y ↦ mt (pointsMap_hom_mem_iff f y).1 (hf y)
  refine eq_zero_of_isEmpty_points (F := G) ((smallBaseChange B S hS i hi.rep).obj V) ?_ _
  refine ⟨fun p ↦ ?_⟩
  refine hVT (pointsMap B S hS _ (yoneda.map (hi.rep.snd V.obj.hom)) p)
    ⟨pointsMap B S hS _ (hi.rep.fst V.obj.hom) p, ?_⟩
  calc pointsMap B S hS Z.1 i.hom (pointsMap B S hS _ (hi.rep.fst V.obj.hom) p)
      = pointsMap B S hS _ (hi.rep.fst V.obj.hom ≫ i.hom) p :=
        (pointsMap_comp_apply B S hS _ _ p).symm
    _ = pointsMap B S hS _ (yoneda.map (hi.rep.snd V.obj.hom) ≫ V.obj.hom) p := by
        rw [hi.rep.w V.obj.hom]
    _ = pointsMap B S hS _ V.obj.hom
          (pointsMap B S hS _ (yoneda.map (hi.rep.snd V.obj.hom)) p) :=
        pointsMap_comp_apply B S hS _ _ p

/-- **Stacks 0A4L.** The functor `H_Z` of a closed immersion `i : Z ⟶ X` of algebraic spaces:
the sections with support in `|Z|`, viewed on the small étale site of `Z` through the inverse
image along `i`.

The first factor is the subsheaf of `F` of sections whose support maps into the point set of
`i`, which is the source's `H_Z(F)`; the second is the inverse image along `i`, which is what
the source means by viewing that subsheaf on `Z_étale`. -/
@[stacks 0A4L "the functor H_Z on abelian sheaves of the small étale site"]
def sectionsWithSupportInClosedSubspace (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1} :=
  letI := (smallBaseChange_isMorphismOfSites B S hS i hi.rep).toIsContinuous
  closedSectionsWithSupport.{u + 1} B S hS i ⋙
    (smallBaseChange B S hS i hi.rep).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)

/-- Sections with support in the point set of a closed immersion, as a functor, is additive;
hence so is the functor `H_Z`, the inverse image being additive. -/
instance sectionsWithSupportInClosedSubspace_additive (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (sectionsWithSupportInClosedSubspace B S hS i hi).Additive :=
  letI := (smallBaseChange_isMorphismOfSites B S hS i hi.rep).toIsContinuous
  letI : ((smallBaseChange B S hS i hi.rep).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)).IsLeftAdjoint :=
    ⟨_, ⟨(smallBaseChange B S hS i hi.rep).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)⟩⟩
  haveI : ((smallBaseChange B S hS i hi.rep).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)).Additive :=
    ((smallBaseChange B S hS i hi.rep).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).left_adjoint_additive
  Functor.instAdditiveComp (closedSectionsWithSupport.{u + 1} B S hS i)
    ((smallBaseChange B S hS i hi.rep).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1))

end ClosedImmersion

end AlgebraicGeometry.Space

end
