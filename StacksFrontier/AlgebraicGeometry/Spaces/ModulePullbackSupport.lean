module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteFromGeneratingSections

/-!
# The support of the pullback of a module of finite type

Let `g : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `F` be an
`𝒪_X`-module of finite type.  Two facts about the support of the pullback `g^*F` of Stacks 03LU
are proved here: it is again of finite type on the site, so its support is closed; and its
support is contained in the inverse image of the support of `F`.  Together they are what the
base-change statement of Stacks 0CZJ consumes.

Finite type is the pullback statement of Stacks 03DO, in the categorical form supplied by
`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteTypeOnSite`, instantiated at the morphism of
small étale ringed topoi of Stacks 03G8.

For the containment of supports, the source of Stacks 0CZJ cites the *equality*
`Supp(g^*F) = |g|⁻¹ Supp(F)` of Stacks 07TZ, part (3).  Only the containment is proved here, and it
is proved without any computation of the stalk of a pullback — which Stacks 07TZ does by
`F_x̄ ⊗_{𝒪_{X, x̄}} 𝒪_{X', x̄'}` and Nakayama — and without assuming `F` quasi-coherent; the full
equality, for quasi-coherent `F`, is
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`.  The argument is a restriction to the
open subspace on which `F` vanishes.  Writing `T` for the support of `F`, closed by Stacks 07TZ, let
`U ⊂ X` be the open subspace on `Tᶜ` of Stacks 03BZ and `W = g⁻¹U ⊂ X'` its inverse image.  Then
`F|_U` has empty support, hence is zero; the restriction of `g^*F` to `W` is the pullback of `F|_U`
along `W ⟶ U`, by the composition comparison of Stacks 03LU applied to the two factorizations of
`W ⟶ X`, hence is zero as well; and the inclusion of `W` is étale, so by Stacks 07TY the support of
`g^*F` misses the point set of `W`, which is `|g|⁻¹(Tᶜ)`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_eq_of_iso`: the support of a module is unchanged by an
  isomorphism of modules.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`: **Stacks 03DO** for the clause
  03DL(5) at a morphism of algebraic spaces, which is also the finite-type conclusion of
  **Stacks 07TZ** part (3).
* `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_of_isEtale`: the support of a pullback
  along an *étale* morphism is the inverse image of the support, for the pullback of
  Stacks 03LU.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_subset`: the containment of supports
  for an arbitrary morphism.

## Implementation notes

The étale case is
`AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback`, which is stated for
`AlgebraicGeometry.Space.etaleModulePullback`, restriction of sections along postcomposition of
étale charts.  Transporting it to `AlgebraicGeometry.Space.modulePullback` is Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, together with
`AlgebraicGeometry.Space.supportOfSheaf_eq_of_iso`.

The inverse image of the open subspace is taken as a `CategoryTheory.Subfunctor.preimage`, not as
the open subspace on the inverse image of the point set: the cartesian square
`CategoryTheory.Subfunctor.isPullback_preimage` is then available for free, and with it both the
étaleness of the inclusion (base change of an étale morphism, Stacks 03FV) and the point set
(`AlgebraicGeometry.Space.range_pointsMap_ι_preimage`, Stacks 03H4).  The two factorizations of
`W ⟶ X` are the two sides of that square.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The support is an invariant of the isomorphism class -/

/-- **The support of an abelian sheaf depends only on its isomorphism class.**  Each of the two
inclusions is `AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono`, Stacks 04KB, applied to
one of the two halves of the isomorphism, which is a monomorphism because it has a retraction. -/
theorem supportOfSheaf_eq_of_isoSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    {A C : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{m}} (e : A ≅ C) :
    supportOfSheaf B S hS X A = supportOfSheaf B S hS X C := by
  exact subset_antisymm (supportOfSheaf_subset_of_mono B S hS X hX e.hom)
    (supportOfSheaf_subset_of_mono B S hS X hX e.inv)

/-- **The support of a module depends only on its isomorphism class.**  This is
`AlgebraicGeometry.Space.supportOfSheaf_eq_of_isoSheaf` at the image of the isomorphism under
`SheafOfModules.toSheaf`. -/
theorem supportOfSheaf_eq_of_iso (X : AlgebraicSpaces B S hS)
    {F G : Modules.{u, m} B S hS X.1 X.2} (e : F ≅ G) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) :=
  supportOfSheaf_eq_of_isoSheaf B S hS X.1 X.property ((SheafOfModules.toSheaf _).mapIso e)

/-! ### Pullback preserves finite type -/

variable {X' X : AlgebraicSpaces B S hS}

/-- **Stacks 03DO for the clause 03DL(5) at a morphism of algebraic spaces.**  The pullback of
Stacks 03LU of an `𝒪_X`-module of finite type on the small étale site is again of finite type on
the small étale site.

This is `Stacks.Sheaves.FiniteType.pullbackModules_isFiniteTypeOnSite` at the morphism of small
étale ringed topoi of Stacks 03G8, through `AlgebraicGeometry.Space.modulePullback_eq`.

It is also the finite-type conclusion of Stacks 07TZ part (3), which the source gets the same
way, by citing the pullback clause of Stacks 03DO; the support conclusion of that part is
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`. -/
theorem isFiniteTypeOnSite_modulePullback (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : SheafOfModules.IsFiniteTypeOnSite F) :
    SheafOfModules.IsFiniteTypeOnSite ((modulePullback B S hS g).obj F) :=
  Stacks.Sheaves.FiniteType.pullbackModules_isFiniteTypeOnSite
    (smallEtaleRingedToposModulesHom B S hS g) F hF

/-! ### The support of a pullback along an étale morphism -/

/-- **The support of a pullback along an étale morphism is the inverse image of the support**,
for the pullback of modules of Stacks 03LU.

Stacks 03LW identifies that pullback with restriction of sections along postcomposition of étale
charts, for which the statement is
`AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback`. -/
theorem supportOfSheaf_modulePullback_of_isEtale (g : X' ⟶ X) (hg : IsEtale B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) =
      pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  rw [supportOfSheaf_eq_of_iso B S hS X'
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).app F)]
  exact supportOfSheaf_toSheaf_etaleModulePullback B S hS g hg F

/-- **The support of the pullback of a module of finite type is closed.**  The pullback is again
of finite type by Stacks 03DO, and the support of a module of finite type is closed by
Stacks 07TZ.

This is what makes the base-change statement of Stacks 0CZJ expressible:
`AlgebraicGeometry.Space.IsProperOver` takes a proof that its subset is closed. -/
theorem isClosed_supportOfSheaf_modulePullback (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : SheafOfModules.IsFiniteTypeOnSite F) :
    IsClosed (supportOfSheaf B S hS X'.1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F))) :=
  have := isFiniteTypeOnSite_modulePullback B S hS g F hF
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X'.1 X'.property _

/-! ### The support of a pullback along an arbitrary morphism -/

/-- **The support of the pullback of a module of finite type is contained in the inverse image
of its support.**

The complement of the support is open, so it carries an open subspace `U` of `X` by
Stacks 03BZ; the restriction of `F` to `U` has empty support and is therefore zero. The
inverse image `W` of `U` in `X'` sits in a cartesian square over `U`, so the restriction of
`g^*F` to `W` is the pullback of the restriction of `F` to `U`, by the composition comparison
of Stacks 03LU, and so is zero too. The inclusion of `W` is étale, being a base change of the
inclusion of `U`, so the support of `g^*F` meets the point set of `W` in the support of that
zero module; and the point set of `W` is the inverse image of the complement of the support of
`F`. -/
theorem supportOfSheaf_modulePullback_subset (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : SheafOfModules.IsFiniteTypeOnSite F) :
    supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) ⊆
      pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  have hT : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) :=
    have := hF
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.property F
  obtain ⟨UA, WA, j, gU, j', hjet, hj'et, hcomm, hUrange, hWrange⟩ :
      ∃ (UA WA : AlgebraicSpaces B S hS) (j : UA ⟶ X) (gU : WA ⟶ UA) (j' : WA ⟶ X'),
        IsEtale B S hS j.hom ∧ IsEtale B S hS j'.hom ∧ j' ≫ g = gU ≫ j ∧
        Set.range (pointsMap B S hS UA.1 j.hom) =
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))ᶜ ∧
        Set.range (pointsMap B S hS WA.1 j'.hom) = pointsMap B S hS X'.1 g.hom ⁻¹'
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))ᶜ := by
    have hUos : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X.1
        (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))ᶜ) :=
      isOpenSubspace_openSubspaceOfPoints B S hS X.property _ hT.isOpen_compl
    have hsqW : IsPullback
        ((openSubspaceOfPoints B S hS X.1
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))ᶜ).fromPreimage g.hom)
        ((openSubspaceOfPoints B S hS X.1
          (supportOfSheaf B S hS X.1
            ((SheafOfModules.toSheaf _).obj F))ᶜ).preimage g.hom).ι
        (openSubspaceOfPoints B S hS X.1
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))ᶜ).ι g.hom :=
      Subfunctor.isPullback_preimage g.hom _
    have hWalg : IsAlgebraicSpace B S hS ((openSubspaceOfPoints B S hS X.1
        (supportOfSheaf B S hS X.1
          ((SheafOfModules.toSheaf _).obj F))ᶜ).preimage g.hom).toFunctor :=
      isAlgebraicSpace_of_isPullback hUos.1 X'.property X.property.isSheaf
        X.property.diagonal_representable hsqW
    have hpull : IsPullback
        (ObjectProperty.homMk ((openSubspaceOfPoints B S hS X.1
            (supportOfSheaf B S hS X.1
              ((SheafOfModules.toSheaf _).obj F))ᶜ).fromPreimage g.hom) :
          (⟨_, hWalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hUos.1⟩)
        (ObjectProperty.homMk ((openSubspaceOfPoints B S hS X.1
          (supportOfSheaf B S hS X.1
            ((SheafOfModules.toSheaf _).obj F))ᶜ).preimage g.hom).ι)
        (ObjectProperty.homMk (openSubspaceOfPoints B S hS X.1
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))ᶜ).ι) g :=
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS P)) hsqW
    refine ⟨⟨_, hUos.1⟩, ⟨_, hWalg⟩, _, _, _, isEtale_ι_of_isOpenSubspace hUos,
      isEtale_of_isPullback B S hS _ _ _ g hpull (isEtale_ι_of_isOpenSubspace hUos),
      hpull.w.symm, range_pointsMap_ι_openSubspaceOfPoints B S hS _, ?_⟩
    exact (range_pointsMap_ι_preimage' B S hS g.hom _).trans
      (congrArg (fun s => pointsMap B S hS X'.1 g.hom ⁻¹' s)
        (range_pointsMap_ι_openSubspaceOfPoints B S hS _))
  -- the restriction of `F` to the open subspace is zero
  have hjzero : IsZero ((modulePullback B S hS j).obj F) := by
    refine isZero_of_supportOfSheaf_eq_empty B S hS UA _ ?_
    rw [supportOfSheaf_modulePullback_of_isEtale B S hS j hjet F,
      Set.eq_empty_iff_forall_notMem]
    intro v hv
    exact (hUrange ▸ Set.mem_range_self v :
      pointsMap B S hS UA.1 j.hom v ∈ (supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj F))ᶜ) hv
  -- the restriction of `g^*F` to the inverse image is the pullback of that, hence zero
  have hiso : (modulePullback B S hS j').obj ((modulePullback B S hS g).obj F) ≅
      (modulePullback B S hS gU).obj ((modulePullback B S hS j).obj F) :=
    (modulePullbackCompIso B S hS j' g).app F ≪≫
      eqToIso (congrArg (fun k : WA ⟶ X => (modulePullback B S hS k).obj F) hcomm) ≪≫
        ((modulePullbackCompIso B S hS gU j).app F).symm
  have hgUadd : (modulePullback B S hS gU).Additive :=
    (modulePullbackAdjunction B S hS gU).left_adjoint_additive
  have hzero : IsZero ((modulePullback B S hS j').obj ((modulePullback B S hS g).obj F)) :=
    (Functor.map_isZero (modulePullback B S hS gU) hjzero).of_iso hiso
  -- hence the support of `g^*F` misses the point set of the inverse image
  have hempty : pointsMap B S hS WA.1 j'.hom ⁻¹'
      supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) = ∅ := by
    rw [← supportOfSheaf_modulePullback_of_isEtale B S hS j' hj'et]
    exact (supportOfSheaf_eq_empty_iff_isZero B S hS WA _).2 hzero
  intro x hx
  by_contra hxT
  obtain ⟨w, hw⟩ : x ∈ Set.range (pointsMap B S hS WA.1 j'.hom) := hWrange ▸ hxT
  refine Set.eq_empty_iff_forall_notMem.1 hempty w ?_
  rw [Set.mem_preimage, hw]
  exact hx

end AlgebraicGeometry.Space

end
