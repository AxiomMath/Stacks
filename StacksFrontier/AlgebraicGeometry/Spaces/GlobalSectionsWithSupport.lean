module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections with support and cohomology with support, for algebraic spaces

Let `X` be an algebraic space over a scheme `S` and let `T` be a set of points of `X`.
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupport.lean` constructs, for an abelian sheaf
`F` on the small étale site of `X`, the subsheaf `H_T(F) ⊆ F` of sections whose support maps into
`T` (Stacks 0A4L), and the endofunctor `H_T` of abelian sheaves it defines.  This file takes the
global sections of that subsheaf and derives the result:

* `Γ_T(X, -)` is `H_T` followed by `CategoryTheory.Sheaf.Γ`, global sections of the small étale
  site.  Its value on `F` is the group of global sections of `F` whose support maps into `T`,
  which for `T` the point set of a closed subspace `Z` is the source's
  `Γ_Z(X, F) = {s ∈ F(X) : Supp(s) ⊆ Z}`.
* `H^q_T(X, -)` is the `q`-th right derived functor of `Γ_T(X, -)`.
* `R H_Z` and `H^q_Z` on abelian sheaves of `Z_étale` are the derived functors of the functor
  `H_Z` of Stacks 0A4L, which this development already has.

Specialised to the point set of a closed immersion `i : Z ⟶ X` these are the `Γ_Z(X, -)`,
`H^q_Z(X, -)`, `R H_Z` and `H^q_Z` of Stacks 0A4L, and in particular they make the vanishing
`H^q_Z(X, F) = 0` of Stacks 0A4R, clause (3), a statement one can write down.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsWithSupport` — the functor `Γ_T(X, -)` from abelian
  sheaves on the small étale site of `X` to abelian groups.
* `AlgebraicGeometry.Space.globalSectionsWithSupportι` and
  `AlgebraicGeometry.Space.globalSectionsWithSupportInclusion` — the comparison
  `Γ_T(X, -) ⟶ Γ(X, -)`, a monomorphism at every sheaf.
* `AlgebraicGeometry.Space.cohomologyWithSupport` — the functor `H^q_T(X, -)`, the `q`-th right
  derived functor of `Γ_T(X, -)`.
* `AlgebraicGeometry.Space.closedGlobalSectionsWithSupport` and
  `AlgebraicGeometry.Space.closedCohomologyWithSupport` — the same for the point set of a closed
  immersion `i : Z ⟶ X`, which is the source's `Γ_Z(X, -)` and `H^q_Z(X, -)`.
* `AlgebraicGeometry.Space.derivedSectionsWithSupportInClosedSubspace` and
  `AlgebraicGeometry.Space.higherSectionsWithSupportInClosedSubspace` — the derived functor
  `R H_Z` and the higher sections with support `H^q_Z`, with values in abelian sheaves on the
  small étale site of `Z`.

## Main results

* `AlgebraicGeometry.Space.sectionSupportedOn_ΓRes_globalSectionsWithSupportι`: a global section
  with support in `T` restricts, on every étale chart, to a section supported on `T`.
* `AlgebraicGeometry.Space.exists_globalSectionsWithSupport`: conversely, a global section all of
  whose chart restrictions are supported on `T` comes from `Γ_T(X, -)`.  Together with the
  previous statement and `AlgebraicGeometry.Space.globalSectionsWithSupportι_mono` this pins the
  construction to the source's definition: `Γ_T(X, F)` *is* the group of global sections of `F`
  with support in `T`.
* `AlgebraicGeometry.Space.globalSectionsWithSupportUnivIso` and
  `AlgebraicGeometry.Space.cohomologyWithSupportUnivIso`: for `T` the whole point set the
  construction collapses to global sections and to
  `AlgebraicGeometry.Space.smallEtaleCohomology`.  This is the structural fact that clause (1)
  of Stacks 0A4R is clause (3) of that lemma for `Z = X`.
* `AlgebraicGeometry.Space.isZero_globalSectionsWithSupport_empty`: for `T` empty the
  construction is zero.  With the previous item this is the check that the functor really does
  depend on `T`.

## Implementation notes

Global sections of the small étale site is Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint
of the constant sheaf functor, the same choice as in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyAffineCriterion.lean`.  The small étale site has
no terminal object — its objects are *scheme* charts — so global sections is not evaluation
anywhere; `Sheaf.Γ` is the limit of the underlying presheaf over the whole site, and that is the
form in which the sectionwise characterisation of `Γ_T(X, F)` is proved, through
`CategoryTheory.Sheaf.isLimitConeΓ` and `CategoryTheory.Limits.Concrete.isLimit_ext`.  Being a
right adjoint, `Sheaf.Γ` is additive and preserves monomorphisms, which is what makes the derived
functors exist and the comparison with `Γ(X, -)` injective.

The coefficients are `AddCommGrpCat.{u + 1}`, the universe in which the small étale site of a
`Scheme.{u}` is a site: that is where sheafification, hence `Sheaf.Γ`, is available, and where
the enough-injectives instance
`AlgebraicGeometry.Space.smallEtaleAbelianSheaf_enoughInjectives` lives.  The subsheaf
construction of Stacks 0A4L is universe-free in the coefficients, and the comparison
`H_univ ≅ 𝟭` is therefore proved at that generality before being specialised.

Derived functors of `Γ_T(X, -)` are Mathlib's `CategoryTheory.Functor.rightDerived`, indexed by
`ℕ`, the same spelling as `AlgebraicGeometry.Space.smallEtaleCohomology`; that is what makes the
comparison of `H^q_T` for `T = Set.univ` with `H^q` a one-liner through
`CategoryTheory.NatTrans.rightDerived`.  The derived functors of `H_Z`, by contrast, are the
`ℤ`-indexed `Functor.rightDerivedPlus` of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean`, because that is
the spelling Stacks 0A4N is already stated in.

Three things the source also states are **not** proved here, each for a named reason.

The degree-zero identification `H^0_T(X, -) ≅ Γ_T(X, -)`:
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` asks for `Γ_T(X, -)` to preserve finite limits.
`Sheaf.Γ` does, being a right adjoint, but left exactness of the subsheaf functor
`AlgebraicGeometry.Space.sectionsWithSupport` is not available — preservation of kernels would
need the support of a section of a subsheaf to agree with its support in the ambient sheaf, and
only one inclusion of that, for the subsheaf of sections with support itself, is proved
(`AlgebraicGeometry.Space.supportOfSection_sectionsWithSupportSheaf_subset`).

The long exact sequence of the pair, that is the triangle
`RΓ_Z(X, -) ⟶ RΓ(X, -) ⟶ RΓ(U, -) ⟶ RΓ_Z(X, -)[1]` with `U` the open complement: the open
complement of a closed subspace is available
(`AlgebraicGeometry.Space.isOpenSubspace_openComplement`) and so is restriction of abelian
sheaves along an étale, hence an open, immersion
(`AlgebraicGeometry.Space.etaleAbelianRestriction`), but the short exact sequence
`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` on an injective abelian sheaf `I` is not: it is the
surjectivity of `I(X) ⟶ I(U)`, Stacks 093X, and the general-site form of that statement,
`Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective`, needs `U` to be
an *object* of the site with `U ⟶ X` a monomorphism there.  An open subspace of an algebraic
space is not an object of the small étale site, so it cannot be instantiated; what would be
needed instead is exactness of `etaleAbelianRestriction` together with the left adjoint `j_!`,
which this development does not construct.

The Grothendieck spectral sequence `E_2^{p,q} = H^p(Z, H^q_Z(F)) ⇒ H^{p+q}_Z(X, F)`: its two
inputs are present — `CategoryTheory.Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp`
and, for the acyclicity hypothesis, `Functor.rightAcyclic_obj_of_preservesInjectiveObjects`
applied to Stacks 0A4M in the form of the functorial statement
`…preservesInjectiveObjects_sectionsWithSupportInClosedSubspace_of_isClosedImmersion`
of `StacksFrontier/AlgebraicGeometry/Spaces/InjectiveSectionsWithSupport.lean`
— but they produce a spectral sequence abutting to the derived functors of the *composite*
`H_Z ⋙ Γ(Z, -)`, global sections on `Z_étale`.  Identifying that with `H^q_Z(X, -)` as defined
here needs `Γ(Z, i⁻¹G) ≅ Γ(X, G)` for a `G` supported on `Z`, which is the global-sections half
of the equivalence of Morphisms of Spaces, Lemma 67.13.5 that the source uses silently; that
comparison is absent, and defining `Γ_Z(X, -)` as the composite instead would be a different
functor from the source's.

No `@[stacks]` attribute is carried: this is substrate for Stacks 0A4L and 0A4R, and no tag is
claimed.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4N](https://stacks.math.columbia.edu/tag/0A4N)
* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

section Univ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Every section is supported on the whole point set: its support is contained in the
preimage of `Set.univ`, which is everything. -/
theorem sectionSupportedOn_univ
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    SectionSupportedOn B S hS X Set.univ F U σ :=
  fun _ _ ↦ Set.mem_univ _

/-- The subsheaf of sections with support in the whole point set is the ambient sheaf: over
every étale chart the support condition is vacuous, so the subgroup is everything. -/
def sectionsWithSupportSheafUnivIso
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    sectionsWithSupportSheaf B S hS X Set.univ F ≅ F :=
  (fullyFaithfulSheafToPresheaf (SmallEtale.topology B S hS X)
      AddCommGrpCat.{v}).preimageIso
    (NatIso.ofComponents
      (fun U ↦ AddEquiv.toAddCommGrpIso
        { toFun := fun σ ↦ σ.1
          invFun := fun σ ↦ ⟨σ, sectionSupportedOn_univ B S hS X F U.unop σ⟩
          left_inv := fun _ ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl })
      (fun _ ↦ by ext; rfl))

/-- **Sections with support in the whole point set are all the sections**, as a natural
isomorphism of endofunctors of the abelian sheaves on the small étale site. -/
def sectionsWithSupportUnivIso :
    sectionsWithSupport B S hS X Set.univ ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :=
  NatIso.ofComponents (sectionsWithSupportSheafUnivIso B S hS X)
    (fun _ ↦ by
      refine Sheaf.hom_ext ?_
      ext U σ
      rfl)

/-- The isomorphism identifying the sections with support in the whole point set with all the
sections is the inclusion of the subsheaf. -/
theorem sectionsWithSupportUnivIso_hom_app
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    (sectionsWithSupportUnivIso B S hS X).hom.app F =
      sectionsWithSupportSheafInclusion B S hS X Set.univ F :=
  rfl

end Univ

section GlobalSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The sections with support `Γ_T(X, -)`.** For a set `T` of points of `X`, the functor
taking an abelian sheaf `F` on the small étale site of `X` to the group of global sections of
`F` whose support maps into `T`: the subsheaf `H_T(F)` of Stacks 0A4L followed by global
sections of the site.

For `T` the point set of a closed subspace `Z ⊆ X` this is the `Γ_Z(X, -)` of Stacks 0A4L. -/
@[sga "2 XIV 1.0" "more general"]
def globalSectionsWithSupport (T : Set (points B S hS X)) :
    Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sectionsWithSupport B S hS X T ⋙ Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}

/-- The sections with support are an additive functor, the two factors being additive; this is
one of the two hypotheses under which its right derived functors are defined. -/
instance globalSectionsWithSupport_additive (T : Set (points B S hS X)) :
    (globalSectionsWithSupport B S hS X T).Additive :=
  inferInstanceAs (Functor.Additive
    (sectionsWithSupport B S hS X T ⋙
      Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}))

/-- The inclusion `Γ_T(X, F) ⟶ Γ(X, F)` of the global sections with support in `T` into all
global sections, at a single sheaf: global sections applied to the inclusion of the subsheaf of
sections with support. -/
abbrev globalSectionsWithSupportι (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}) :
    (globalSectionsWithSupport B S hS X T).obj F ⟶
      (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).obj F :=
  (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map
    ((sectionsWithSupportInclusion B S hS X T).app F)

/-- The inclusion `Γ_T(X, F) ⟶ Γ(X, F)` is natural in `F`, the inclusion of the subsheaf of
sections with support being natural. -/
theorem globalSectionsWithSupportι_naturality (T : Set (points B S hS X))
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (globalSectionsWithSupport B S hS X T).map φ ≫ globalSectionsWithSupportι B S hS X T G =
      globalSectionsWithSupportι B S hS X T F ≫
        (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map φ :=
  ((Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map_comp _ _).symm.trans
    (((congrArg (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map
        ((sectionsWithSupportInclusion B S hS X T).naturality φ))).trans
      ((Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map_comp _ _))

/-- The comparison `Γ_T(X, -) ⟶ Γ(X, -)` from the sections with support to all global
sections, as a morphism of functors. -/
def globalSectionsWithSupportInclusion (T : Set (points B S hS X)) :
    globalSectionsWithSupport B S hS X T ⟶
      Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1} where
  app F := globalSectionsWithSupportι B S hS X T F
  naturality _ _ φ := globalSectionsWithSupportι_naturality B S hS X T φ

/-- The comparison `Γ_T(X, F) ⟶ Γ(X, F)` is a monomorphism: the global sections with support
in `T` form a subgroup of the global sections.  Global sections is a right adjoint, so it
preserves the monomorphism `H_T(F) ⟶ F`. -/
instance globalSectionsWithSupportι_mono (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}) :
    Mono (globalSectionsWithSupportι B S hS X T F) :=
  inferInstanceAs (Mono ((Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map
    ((sectionsWithSupportInclusion B S hS X T).app F)))

/-- Restricting a global section with support to an étale chart and then forgetting the
support condition is the same as forgetting it first: the restriction maps of the subsheaf of
sections with support are the restriction maps of the ambient sheaf. -/
theorem globalSectionsWithSupportι_comp_ΓRes (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS X) :
    globalSectionsWithSupportι B S hS X T F ≫ F.ΓRes (op U) =
      ((sectionsWithSupport B S hS X T).obj F).ΓRes (op U) ≫
        ((sectionsWithSupportInclusion B S hS X T).app F).hom.app (op U) :=
  Sheaf.ΓRes_naturality ((sectionsWithSupportInclusion B S hS X T).app F) (op U)

/-- **A global section with support in `T` is supported on `T` over every étale chart.**

This is one half of the identification of `Γ_T(X, F)` with the source's group
`{s ∈ F(X) : Supp(s) ⊆ T}`; the other half is
`AlgebraicGeometry.Space.exists_globalSectionsWithSupport`. -/
theorem sectionSupportedOn_ΓRes_globalSectionsWithSupportι (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS X)
    (s : (globalSectionsWithSupport B S hS X T).obj F) :
    SectionSupportedOn B S hS X T F U
      ((globalSectionsWithSupportι B S hS X T F ≫ F.ΓRes (op U)) s) := by
  rw [globalSectionsWithSupportι_comp_ΓRes]
  exact (((sectionsWithSupport B S hS X T).obj F).ΓRes (op U) s).2

/-- **A global section whose restriction to every étale chart is supported on `T` is a global
section with support in `T`.**

Global sections of the small étale site is a limit over the whole site
(`CategoryTheory.Sheaf.isLimitConeΓ`), and the forgetful functor to types preserves that limit,
so a compatible family of sections of the subsheaf of sections with support is a global section
of it; the two global sections of `F` then agree because the restrictions to the charts are
jointly injective, again by the limit property.

With `AlgebraicGeometry.Space.sectionSupportedOn_ΓRes_globalSectionsWithSupportι` and
`AlgebraicGeometry.Space.globalSectionsWithSupportι_mono` this identifies `Γ_T(X, F)` with the
source's group `{s ∈ F(X) : Supp(s) ⊆ T}`. -/
theorem exists_globalSectionsWithSupport (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (t : (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).obj F)
    (ht : ∀ U : SmallEtale B S hS X,
      SectionSupportedOn B S hS X T F U (F.ΓRes (op U) t)) :
    ∃ s : (globalSectionsWithSupport B S hS X T).obj F,
      globalSectionsWithSupportι B S hS X T F s = t := by
  let σ : (((sectionsWithSupport B S hS X T).obj F).obj ⋙
      forget AddCommGrpCat.{u + 1}).sections :=
    ⟨fun U ↦ ⟨F.ΓRes U t, ht U.unop⟩,
      fun {_ _} g ↦ Subtype.ext (ConcreteCategory.congr_hom (F.ΓRes_map g) t)⟩
  let hl := isLimitOfPreserves (forget AddCommGrpCat.{u + 1})
    (Sheaf.isLimitConeΓ ((sectionsWithSupport B S hS X T).obj F))
  refine ⟨(Types.isLimitEquivSections hl).symm σ, ?_⟩
  refine Concrete.isLimit_ext F.obj (Sheaf.isLimitConeΓ F) _ _ fun U ↦ ?_
  calc F.coneΓ.π.app U
        (globalSectionsWithSupportι B S hS X T F ((Types.isLimitEquivSections hl).symm σ))
      = ((sectionsWithSupportInclusion B S hS X T).app F).hom.app U
          (((sectionsWithSupport B S hS X T).obj F).coneΓ.π.app U
            ((Types.isLimitEquivSections hl).symm σ)) :=
        ConcreteCategory.congr_hom
          (globalSectionsWithSupportι_comp_ΓRes B S hS X T F U.unop) _
    _ = ((sectionsWithSupportInclusion B S hS X T).app F).hom.app U (σ.1 U) :=
        congrArg _ (Types.isLimitEquivSections_symm_apply hl σ U)
    _ = F.coneΓ.π.app U t := rfl

/-- **Global sections with support in the whole point set are the global sections.** Every
section is supported on all of `X`, so the subsheaf of sections with support is the ambient
sheaf and the sections with support are the global sections. -/
def globalSectionsWithSupportUnivIso :
    globalSectionsWithSupport B S hS X Set.univ ≅
      Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight (sectionsWithSupportUnivIso B S hS X)
      (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}) ≪≫
    (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).leftUnitor

/-- **Cohomology with support `H^q_T(X, -)`.** The `q`-th right derived functor of the sections
with support `Γ_T(X, -)`.

For `T` the point set of a closed subspace `Z ⊆ X` this is the `H^q_Z(X, -)` of Stacks 0A4L,
the cohomology with support whose vanishing in degrees `> d` is clause (3) of Stacks 0A4R. -/
def cohomologyWithSupport (T : Set (points B S hS X)) (q : ℕ) :
    Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (globalSectionsWithSupport B S hS X T).rightDerived q

/-- **Cohomology with support in the whole point set is cohomology.** The structural
identification of clause (1) of Stacks 0A4R — the vanishing of `H^q(X, F)` — with clause (3) of
that lemma — the vanishing of `H^q_Z(X, F)` for `Z` with quasi-compact complement — taken at
`Z = X`, whose complement is empty and hence quasi-compact. -/
def cohomologyWithSupportUnivIso (q : ℕ) :
    cohomologyWithSupport B S hS X Set.univ q ≅ smallEtaleCohomology B S hS X q where
  hom := NatTrans.rightDerived (globalSectionsWithSupportUnivIso B S hS X).hom q
  inv := NatTrans.rightDerived (globalSectionsWithSupportUnivIso B S hS X).inv q
  hom_inv_id := by
    dsimp only [cohomologyWithSupport, smallEtaleCohomology]
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    dsimp only [cohomologyWithSupport, smallEtaleCohomology]
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

/-! ### Sections with support in no point at all -/

/-- The subsheaf of sections with support in the empty set of points is zero: a section with
empty support vanishes. -/
theorem isZero_sectionsWithSupportSheaf_empty
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}) :
    IsZero (sectionsWithSupportSheaf B S hS X (∅ : Set (points B S hS X)) F) := by
  rw [IsZero.iff_id_eq_zero]
  refine Sheaf.hom_ext ?_
  ext U σ
  refine Subtype.ext (eq_zero_of_supportOfSection_eq_empty U.unop σ.1 ?_)
  have hσ : supportOfSection B S hS X F U.unop σ.1 ⊆
      pointsMap B S hS _ U.unop.obj.hom ⁻¹' (∅ : Set (points B S hS X)) := σ.2
  rw [Set.preimage_empty] at hσ
  exact Set.subset_empty_iff.1 hσ

/-- **Global sections with support in the empty set of points vanish.** Together with
`AlgebraicGeometry.Space.globalSectionsWithSupportUnivIso` this shows that the construction
really does depend on the set of points, and is neither the zero functor nor global
sections. -/
theorem isZero_globalSectionsWithSupport_empty
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}) :
    IsZero ((globalSectionsWithSupport B S hS X (∅ : Set (points B S hS X))).obj F) :=
  (Sheaf.Γ (SmallEtale.topology B S hS X) AddCommGrpCat.{u + 1}).map_isZero
    (isZero_sectionsWithSupportSheaf_empty B S hS X F)

end GlobalSections

section ClosedImmersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **The sections with support `Γ_Z(X, -)` of Stacks 0A4L**, for a closed immersion
`i : Z ⟶ X` of algebraic spaces over `S`: the global sections of an abelian sheaf on the small
étale site of `X` whose support maps into the point set of `i`. -/
@[sga "2 XIV 1.0" "more general"]
abbrev closedGlobalSectionsWithSupport (i : Z ⟶ X) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  globalSectionsWithSupport B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom))

/-- **The cohomology with support `H^q_Z(X, -)` of Stacks 0A4L**, for a closed immersion
`i : Z ⟶ X` of algebraic spaces over `S`: the `q`-th right derived functor of
`AlgebraicGeometry.Space.closedGlobalSectionsWithSupport`.

Its vanishing in degrees `> d` is clause (3) of Stacks 0A4R, for `X` of dimension at most `d`
and `Z` with quasi-compact complement. -/
abbrev closedCohomologyWithSupport (i : Z ⟶ X) (q : ℕ) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  cohomologyWithSupport B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom)) q

end ClosedImmersion

section DerivedSheaves

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **The derived functor `R H_Z` of Stacks 0A4L**, from the bounded below derived category of
abelian sheaves on the small étale site of `X` to that of `Z`. -/
def derivedSectionsWithSupportInClosedSubspace (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    DerivedCategory.Plus (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1}) :=
  (sectionsWithSupportInClosedSubspace B S hS i hi).rightDerivedFunctorPlus

/-- **The higher sections with support `H^q_Z` of Stacks 0A4L**: the `q`-th right derived
functor of `H_Z`, with values in abelian sheaves on the small étale site of `Z`.

This is the functor whose vanishing on a direct image of an injective sheaf is Stacks 0A4N,
`AlgebraicGeometry.Space.isZero_rightDerivedPlus_sectionsWithSupportInClosedSubspace`, and
whose values are the `E_2`-terms of the spectral sequence of Stacks 0A4L. -/
def higherSectionsWithSupportInClosedSubspace (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (q : ℤ) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1} :=
  (sectionsWithSupportInClosedSubspace B S hS i hi).rightDerivedPlus q

end DerivedSheaves

section Usability

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- `H^q_Z(X, F)` is an abelian group, for `X` the algebraic space represented by a scheme over
-- `S`, `i : Z ⟶ X` a closed immersion and `F` an abelian sheaf on the small étale site of `X`.
example (T : BigFppfOver B S hS) {Z : AlgebraicSpaces B S hS}
    (i : Z ⟶ yonedaSpace B S hS T)
    (F : Sheaf (SmallEtale.topology B S hS (yonedaSpace B S hS T).1)
      AddCommGrpCat.{u + 1}) (q : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (closedCohomologyWithSupport B S hS i q).obj F

-- The conclusion of Stacks 0A4R, clause (3), is now a statement one can write down: the
-- cohomology with support in a closed subspace vanishes in degrees above the dimension bound.
-- This records only that the assertion is expressible; nothing here proves it.
example (T : BigFppfOver B S hS) {Z : AlgebraicSpaces B S hS}
    (i : Z ⟶ yonedaSpace B S hS T) (d : ℕ) : Prop :=
  ∀ (F : Sheaf (SmallEtale.topology B S hS (yonedaSpace B S hS T).1)
      AddCommGrpCat.{u + 1}) (q : ℕ), d < q →
    IsZero ((closedCohomologyWithSupport B S hS i q).obj F)

-- The same vanishing with `Z = X` is the conclusion of clause (1), through
-- `AlgebraicGeometry.Space.cohomologyWithSupportUnivIso`.
example (T : BigFppfOver B S hS)
    (F : Sheaf (SmallEtale.topology B S hS (yonedaSpace B S hS T).1)
      AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : IsZero ((cohomologyWithSupport B S hS (yonedaSpace B S hS T).1
      Set.univ q).obj F)) :
    IsZero ((smallEtaleCohomology B S hS (yonedaSpace B S hS T).1 q).obj F) :=
  h.of_iso ((cohomologyWithSupportUnivIso B S hS
    (yonedaSpace B S hS T).1 q).symm.app F)

end Usability

end AlgebraicGeometry.Space

end
