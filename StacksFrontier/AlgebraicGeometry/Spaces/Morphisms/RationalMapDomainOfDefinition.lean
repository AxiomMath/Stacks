module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparatedEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# The domain of definition of a rational map of algebraic spaces

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site, with `X`
reduced and `Y` separated over `S`. A rational map `φ` from `X` to `Y` is a class of morphisms
defined on dense open subspaces of `X`, and the open subspace `U ⊆ X` whose point set is the
domain of definition of Stacks 0EMQ carries exactly one morphism `U ⟶ Y` representing `φ`.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_inf`: the intersection of two open subspaces of an
  algebraic space is an open subspace.
* `AlgebraicGeometry.Space.isDenseOpenSubspace_of_eq_domainOfDefinition`: the open subspace
  cut out by the domain of definition is a dense open subspace.
* `AlgebraicGeometry.Space.existsUnique_hom_of_eq_domainOfDefinition` is **Stacks 0EMR**: a
  rational map from a reduced algebraic space to an algebraic space separated over the base is
  represented by a unique morphism on the open subspace of its domain of definition.

## Implementation notes

Two representatives agree on the intersection of their domains: that intersection is an open
subspace, reduced because `X` is, and the common dense open subspace on which the two
representatives agree is dense in it, so Stacks 084N —
`AlgebraicGeometry.Space.eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top` — applies once
the scheme-theoretic closure of that dense open subspace is known to be everything. The latter
is Stacks 03JJ: the scheme-theoretic image is a closed subspace whose point set contains a
dense set, hence is all points, and a closed subspace of a reduced algebraic space with all
points is the whole space. The same argument gives the uniqueness clause on `U` itself.

The representatives are glued without any fpqc descent. Choosing for each point of a scheme
atlas of `U` a representative defined there gives a family of open subspaces of `U`, indexed in
the universe of the site's schemes by `AlgebraicGeometry.Space.pointsToScheme`, whose point
sets cover; by Stacks 03BZ it is a Zariski covering, so the inclusion of the supremum `V` of the
family is locally surjective and `V` sheafifies to everything. On `V` the glued morphism is
defined section by section, which is legitimate because the representatives agree, and it
extends uniquely to `U` by `CategoryTheory.Subfunctor.sheafifyLift`, `Y` being a sheaf. Adding
one further member for an arbitrary fixed representative makes the glued morphism visibly
represent `φ`.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
* [Stacks Project, Tag 0EMQ](https://stacks.math.columbia.edu/tag/0EMQ)
* [Stacks Project, Tag 0EMR](https://stacks.math.columbia.edu/tag/0EMR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The intersection of two open subspaces is an open subspace. -/
theorem isOpenSubspace_inf (hX : IsAlgebraicSpace B S hS X) (V W : Subfunctor X)
    (hV : IsOpenSubspace B S hS V) (hW : IsOpenSubspace B S hS W) :
    IsOpenSubspace B S hS (V ⊓ W) := by
  set P := openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor V.ι) ∩
        Set.range (pointsMap B S hS W.toFunctor W.ι)) with hPdef
  have hPopen : IsOpenSubspace B S hS P :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2).inter
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2))
  have hPV : P ≤ V := by
    refine le_of_range_pointsMap_ι_subset B S hS hV ?_
    rw [hPdef, range_pointsMap_ι_openSubspaceOfPoints]
    exact Set.inter_subset_left
  have hPW : P ≤ W := by
    refine le_of_range_pointsMap_ι_subset B S hS hW ?_
    rw [hPdef, range_pointsMap_ι_openSubspaceOfPoints]
    exact Set.inter_subset_right
  have hle : V ⊓ W ≤ P := by
    refine le_of_range_pointsMap_ι_subset B S hS hPopen ?_
    rw [hPdef, range_pointsMap_ι_openSubspaceOfPoints]
    rintro x ⟨p, rfl⟩
    refine ⟨⟨pointsMap B S hS _ (Subfunctor.homOfLe (inf_le_left : V ⊓ W ≤ V)) p, ?_⟩,
      ⟨pointsMap B S hS _ (Subfunctor.homOfLe (inf_le_right : V ⊓ W ≤ W)) p, ?_⟩⟩ <;>
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  rwa [le_antisymm hle (le_inf hPV hPW)]

/-- A dense set of points of `X` stays dense inside an open subspace of `X` containing the
subspace it is the point set of. -/
private theorem dense_range_pointsMap_homOfLe {P W : Subfunctor X}
    (hP : IsOpenSubspace B S hS P) (hWP : W ≤ P)
    (hdense : Dense (Set.range (pointsMap B S hS W.toFunctor W.ι))) :
    Dense (Set.range (pointsMap B S hS W.toFunctor (Subfunctor.homOfLe hWP))) := by
  have hfac : ∀ w, pointsMap B S hS W.toFunctor W.ι w =
      pointsMap B S hS P.toFunctor P.ι
        (pointsMap B S hS W.toFunctor (Subfunctor.homOfLe hWP) w) := by
    intro w
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  rw [dense_iff_inter_open]
  rintro O hO ⟨p₀, hp₀⟩
  obtain ⟨x, ⟨p, hpO, hpx⟩, w, hw⟩ := hdense.inter_open_nonempty _
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS P.ι hP.2 O hO) ⟨_, Set.mem_image_of_mem _ hp₀⟩
  refine ⟨p, hpO, w, pointsMap_injective_of_mono B S hS P.ι ?_⟩
  rw [← hfac, hw, hpx]

/-- In a reduced algebraic space the scheme-theoretic closure of a subfunctor whose point
set is dense is the whole space. -/
theorem schemeTheoreticImageSubfunctor_ι_eq_top_of_dense
    (hX : IsAlgebraicSpace B S hS X)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (V : Subfunctor X)
    (hdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι))) :
    schemeTheoreticImageSubfunctor B S hS V.ι = ⊤ := by
  set Z := schemeTheoreticImageSubfunctor B S hS V.ι
  have hZ : IsClosedSubspace B S hS Z :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS V.ι hX
  have hVZ : Subfunctor.range V.ι ≤ Z := range_le_schemeTheoreticImageSubfunctor B S hS V.ι
  have hsub : Set.range (pointsMap B S hS V.toFunctor V.ι) ⊆
      Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    rintro x ⟨p, rfl⟩
    refine ⟨pointsMap B S hS V.toFunctor
      (Subfunctor.toRange V.ι ≫ Subfunctor.homOfLe hVZ) p, ?_⟩
    rw [← pointsMap_comp_apply, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  have hfull : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = Set.univ := by
    refine Set.eq_univ_iff_forall.2 fun x ↦ closure_minimal hsub
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX Z.ι hZ.2) ?_
    rw [hdense.closure_eq]
    trivial
  obtain ⟨l, hl⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX hX Z hZ
    hXred (𝟙 X)).2 (hfull ▸ Set.subset_univ _)
  refine le_antisymm le_top fun T x _ ↦ ?_
  have hval : (l.app T x).1 = x := congrArg (fun k : X ⟶ X => k.app T x) hl
  exact hval ▸ (l.app T x).2

/-- Two morphisms from a reduced algebraic space to an algebraic space separated over the base
which agree on an open subspace with dense point set are equal. -/
private theorem eq_of_restrict_eq_of_dense
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hYsep : IsSeparatedOver B S hS Y)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V)
    (hdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)))
    (f g : X ⟶ Y) (heq : V.ι ≫ f = V.ι ≫ g) : f = g := by
  let T₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT₀ : IsTerminal (yoneda.obj T₀) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  exact eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top B S hS
    (isAlgebraicSpace_yoneda B S hS T₀) hX hY (hT₀.from X) (hT₀.from Y) f g
    (hT₀.hom_ext _ _) (hT₀.hom_ext _ _) V hV heq
    (schemeTheoreticImageSubfunctor_ι_eq_top_of_dense B S hS hX hXred V hdense)
    (isSeparated_of_isSeparatedOver B S hS hYsep _)

/-- The point set of the range of the inclusion of a dense open subspace into a larger open
subspace is dense in the larger one. -/
private theorem dense_range_pointsMap_ι_range_homOfLe {P W : Subfunctor X}
    (hP : IsOpenSubspace B S hS P) (hWP : W ≤ P)
    (hdense : Dense (Set.range (pointsMap B S hS W.toFunctor W.ι))) :
    Dense (Set.range (pointsMap B S hS
      (Subfunctor.range (Subfunctor.homOfLe hWP)).toFunctor
      (Subfunctor.range (Subfunctor.homOfLe hWP)).ι)) := by
  rw [range_pointsMap_ι_range B S hS (Subfunctor.homOfLe hWP)]
  exact dense_range_pointsMap_homOfLe B S hS hP hWP hdense

/-- Reducedness passes to an open subspace. -/
private theorem hasEtaleLocalProperty_isReduced_of_isOpenSubspace
    (hX : IsAlgebraicSpace B S hS X)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) :
    HasEtaleLocalProperty B S hS V.toFunctor (fun T : Scheme.{u} => IsReduced T) := by
  rw [exists_atlas_iff_forall_etale B S hS V.toFunctor _ hV.1]
  intro T g hg
  refine (exists_atlas_iff_forall_etale B S hS X _ hX).1 hXred T (g ≫ V.ι) ?_
  set Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have _ : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toIsStableUnderComposition
  have _ : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  exact MorphismProperty.comp_mem Q.presheaf _ _ hg
    (MorphismProperty.relative_monotone (F := yoneda)
      (fun _ _ _ hk => @AlgebraicGeometry.Etale.instOfIsOpenImmersion _ _ _ hk) _ hV.2)

/-- Two morphisms from an open subspace `P` of a reduced algebraic space to an algebraic space
separated over the base which agree on a dense open subspace `W ≤ P` are equal. -/
private theorem eq_of_homOfLe_comp_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hYsep : IsSeparatedOver B S hS Y) {P W : Subfunctor X} (hP : IsOpenSubspace B S hS P)
    (hWP : W ≤ P) (hW : IsDenseOpenSubspace B S hS hX W) (f f' : P.toFunctor ⟶ Y)
    (heq : Subfunctor.homOfLe hWP ≫ f = Subfunctor.homOfLe hWP ≫ f') : f = f' := by
  refine eq_of_restrict_eq_of_dense B S hS hP.1 hY
    (hasEtaleLocalProperty_isReduced_of_isOpenSubspace B S hS hX hXred P hP) hYsep
    (Subfunctor.range (Subfunctor.homOfLe hWP)) (isOpenSubspace_of_le B S hS W P hW.1 hWP)
    (dense_range_pointsMap_ι_range_homOfLe B S hS hP hWP hW.2) f f' ?_
  refine (cancel_epi (Subfunctor.toRange (Subfunctor.homOfLe hWP))).1 ?_
  simpa only [← Category.assoc, Subfunctor.toRange_ι] using heq

/-- Two representatives of one rational map from a reduced algebraic space to an algebraic
space separated over the base take the same value at a common section of their domains. -/
private theorem hom_app_eq_of_toRationalMap_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hYsep : IsSeparatedOver B S hS Y)
    (f g : PartialMap B S hS hX Y)
    (hfg : f.toRationalMap B S hS = g.toRationalMap B S hS)
    (T : (BigFppfOver B S hS)ᵒᵖ) (a : (f.domain.obj T : Type u)) (b : (g.domain.obj T : Type u))
    (hab : (a : X.obj T) = (b : X.obj T)) :
    f.hom.app T a = g.hom.app T b := by
  obtain ⟨W, hW, hWf, hWg, hWeq⟩ := (PartialMap.toRationalMap_eq_iff B S hS).1 hfg
  have hP : IsOpenSubspace B S hS (f.domain ⊓ g.domain) :=
    isOpenSubspace_inf B S hS hX _ _ f.dense_open_domain.1 g.dense_open_domain.1
  have hWP : W ≤ f.domain ⊓ g.domain := le_inf hWf hWg
  have hPY := eq_of_homOfLe_comp_eq B S hS hX hY hXred hYsep hP hWP hW
    (Subfunctor.homOfLe inf_le_left ≫ f.hom) (Subfunctor.homOfLe inf_le_right ≫ g.hom) hWeq
  have hmemP : (a : X.obj T) ∈ (f.domain ⊓ g.domain).obj T := ⟨a.2, hab ▸ b.2⟩
  exact (congrArg (fun k : (f.domain ⊓ g.domain).toFunctor ⟶ Y =>
    k.app T ⟨(a : X.obj T), hmemP⟩) hPY).trans (congrArg (g.hom.app T) (Subtype.ext hab))

/-- The domain of a representative of a rational map is contained in any open subspace whose
point set is the domain of definition, factorization through an open subspace being detected on
points (Stacks 03IE). -/
private theorem domain_le_of_eq_domainOfDefinition
    (hX : IsAlgebraicSpace B S hS X) (φ : RationalMap B S hS hX Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUdom : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      RationalMap.domainOfDefinition B S hS φ)
    (g : PartialMap B S hS hX Y) (hg : g.toRationalMap B S hS = φ) : g.domain ≤ U := by
  refine le_of_range_pointsMap_ι_subset B S hS hU ?_
  rw [hUdom]
  rintro x ⟨p, rfl⟩
  exact ⟨g, hg, ⟨p, rfl⟩⟩

/-- An open subspace of an algebraic space whose point set is the domain of definition of a
rational map is a dense open subspace: it contains the dense domain of every representative. -/
theorem isDenseOpenSubspace_of_eq_domainOfDefinition
    (hX : IsAlgebraicSpace B S hS X) (φ : RationalMap B S hS hX Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUdom : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      RationalMap.domainOfDefinition B S hS φ) :
    IsDenseOpenSubspace B S hS hX U := by
  obtain ⟨g, hg⟩ := RationalMap.exists_rep B S hS φ
  refine ⟨hU, g.dense_open_domain.2.mono ?_⟩
  rintro x ⟨p, rfl⟩
  refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe
    (domain_le_of_eq_domainOfDefinition B S hS hX φ U hU hUdom g hg)) p, ?_⟩
  rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]

/-- Two morphisms on a dense open subspace of a reduced algebraic space into an algebraic space
separated over the base which represent the same rational map are equal. -/
private theorem hom_eq_of_toRationalMap_eq
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hYsep : IsSeparatedOver B S hS Y) {U : Subfunctor X}
    (hUd hUd' : IsDenseOpenSubspace B S hS hX U) (f f' : U.toFunctor ⟶ Y)
    (h : PartialMap.toRationalMap B S hS (⟨U, hUd, f⟩ : PartialMap B S hS hX Y) =
      PartialMap.toRationalMap B S hS (⟨U, hUd', f'⟩ : PartialMap B S hS hX Y)) : f = f' := by
  obtain ⟨W, hW, hWf, hWg, hWeq⟩ := (PartialMap.toRationalMap_eq_iff B S hS).1 h
  exact eq_of_homOfLe_comp_eq B S hS hX hY hXred hYsep hUd.1 hWf hW f f' hWeq

/-- A family of open subspaces of an open subspace `U` whose point sets cover the points of `U`
has a supremum which sheafifies to all of `U`. -/
private theorem sheafify_iSup_eq_top_of_iUnion_range_eq_univ {U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) {K : Type u} (E : K → Subfunctor U.toFunctor)
    (hEopen : ∀ o, IsOpenSubspace B S hS (E o))
    (hcover : (⋃ o, Set.range (pointsMap B S hS (E o).toFunctor (E o).ι)) = Set.univ) :
    Subfunctor.sheafify (BigFppfOver.topology B S hS) (⨆ o, E o) = ⊤ := by
  set J := BigFppfOver.topology B S hS
  have hzar : IsZariskiCover B S hS K E :=
    (isZariskiCover_iff_iUnion_points B S hS U.toFunctor hU.1 K E hEopen).2 hcover
  have hzarsurj : Presheaf.IsLocallySurjective J (Sigma.desc fun o ↦ (E o).ι) := hzar.2
  have hdescfac : (Sigma.desc fun o ↦ (E o).ι) =
      (Sigma.desc fun o ↦ Subfunctor.homOfLe (le_iSup E o)) ≫ (⨆ o, E o).ι := by
    refine Sigma.hom_ext _ _ fun o ↦ ?_
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc, Subfunctor.homOfLe_ι]
  refine le_antisymm le_top fun T x _ ↦ ?_
  show (⨆ o, E o).sieveOfSection x ∈ J (Opposite.unop T)
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J (Sigma.desc fun o ↦ (E o).ι) x)
  rintro T' b ⟨w, hw⟩
  show U.toFunctor.map b.op x ∈ (⨆ o, E o).obj (Opposite.op T')
  rw [← hw, hdescfac]
  exact ((Sigma.desc fun o ↦ Subfunctor.homOfLe (le_iSup E o)).app (Opposite.op T') w).2

/-- A morphism into a sheaf from a subfunctor whose sheafification is everything extends to the
whole presheaf. -/
private theorem exists_ι_comp_eq_of_sheafify_eq_top {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G : Cᵒᵖ ⥤ Type u} {V : Subfunctor F}
    (hV : V.sheafify J = ⊤) (hG : Presieve.IsSheaf J G) (k : V.toFunctor ⟶ G) :
    ∃ f : F ⟶ G, V.ι ≫ f = k := by
  have := (Subfunctor.eq_top_iff_isIso _).1 hV
  refine ⟨inv (V.sheafify J).ι ≫ Subfunctor.sheafifyLift V k hG, ?_⟩
  rw [← Subfunctor.homOfLe_ι (V.le_sheafify J), Category.assoc,
    ← Category.assoc (V.sheafify J).ι, IsIso.hom_inv_id, Category.id_comp]
  exact Subfunctor.to_sheafifyLift V k hG

/-- Representatives of one rational map from a reduced algebraic space to an algebraic space
separated over the base glue to a morphism on any subfunctor of `U` all of whose sections lie in
the domain of some representative. -/
private theorem exists_hom_of_forall_exists_rep
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hYsep : IsSeparatedOver B S hS Y) {φ : RationalMap B S hS hX Y} {U : Subfunctor X}
    {K : Type u} (rep : K → PartialMap B S hS hX Y)
    (hrep : ∀ o, (rep o).toRationalMap B S hS = φ) (V : Subfunctor U.toFunctor)
    (hV : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : (V.toFunctor.obj T : Type u)),
      ∃ o : K, ∃ c : ((rep o).domain.obj T : Type u),
        (c : X.obj T) = ((x : (U.toFunctor.obj T : Type u)) : X.obj T)) :
    ∃ k : V.toFunctor ⟶ Y, ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : (V.toFunctor.obj T : Type u))
      (o : K) (c : ((rep o).domain.obj T : Type u)),
      (c : X.obj T) = ((x : (U.toFunctor.obj T : Type u)) : X.obj T) →
        k.app T x = (rep o).hom.app T c := by
  choose idx wit hwit using hV
  have hglue : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : (V.toFunctor.obj T : Type u)) (o : K)
      (c : ((rep o).domain.obj T : Type u)),
      (c : X.obj T) = ((x : (U.toFunctor.obj T : Type u)) : X.obj T) →
      (rep (idx T x)).hom.app T (wit T x) = (rep o).hom.app T c := fun T x o c hc ↦
    hom_app_eq_of_toRationalMap_eq B S hS hX hY hXred hYsep _ _
      ((hrep (idx T x)).trans (hrep o).symm) T (wit T x) c ((hwit T x).trans hc.symm)
  refine ⟨{ app := fun T ↦ ↾fun x ↦ (rep (idx T x)).hom.app T (wit T x)
            naturality := ?_ }, hglue⟩
  intro T T' b
  ext x
  show (rep (idx T' (V.toFunctor.map b x))).hom.app T' (wit T' (V.toFunctor.map b x)) =
    Y.map b ((rep (idx T x)).hom.app T (wit T x))
  exact (hglue T' (V.toFunctor.map b x) (idx T x)
    ((rep (idx T x)).domain.toFunctor.map b (wit T x)) (congrArg (X.map b) (hwit T x))).trans
    (NatTrans.naturality_apply (rep (idx T x)).hom b (wit T x))

/-- Every point of the open subspace whose point set is the domain of definition of a rational
map lies in the domain of some representative, from a family indexed in the universe of the
site. -/
private theorem exists_rep_cover_of_eq_domainOfDefinition
    (hX : IsAlgebraicSpace B S hS X) (φ : RationalMap B S hS hX Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUdom : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      RationalMap.domainOfDefinition B S hS φ) :
    ∃ (K : Type u) (rep : K → PartialMap B S hS hX Y),
      (∀ o, (rep o).toRationalMap B S hS = φ) ∧ ∀ z, ∃ o,
        pointsMap B S hS U.toFunctor U.ι z ∈
          Set.range (pointsMap B S hS (rep o).domain.toFunctor (rep o).domain.ι) := by
  obtain ⟨A, atl, hatlSurj, -⟩ := hU.1.exists_atlas
  have hatlPoints : Function.Surjective (pointsMap B S hS (yoneda.obj A) atl) :=
    (surjective_iff_surjective_pointsMap B S hS U.toFunctor hU.1 A atl).1 hatlSurj
  choose sec hsec using fun y ↦ surjective_pointsToScheme B S hS A y
  have hdefined : ∀ y : ((BigFppfOver.toScheme B S hS).obj A : Type u),
      ∃ g : PartialMap B S hS hX Y, g.toRationalMap B S hS = φ ∧
        pointsMap B S hS U.toFunctor U.ι
            (pointsMap B S hS (yoneda.obj A) atl (sec y)) ∈
          Set.range (pointsMap B S hS g.domain.toFunctor g.domain.ι) := by
    intro y
    have hmem : pointsMap B S hS U.toFunctor U.ι
        (pointsMap B S hS (yoneda.obj A) atl (sec y)) ∈
        RationalMap.domainOfDefinition B S hS φ := by
      rw [← hUdom]
      exact ⟨_, rfl⟩
    exact hmem
  choose γ hγ hγmem using hdefined
  refine ⟨_, γ, hγ, fun z ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hatlPoints z
  set y := pointsToScheme B S hS A p with hy
  have hsecy : sec y = p := injective_pointsToScheme B S hS A ((hsec y).trans hy)
  exact ⟨y, hsecy ▸ hγmem y⟩

/-- Subspaces of `U` whose point sets cover the points of `U` give, as subfunctors of `U`, a
family whose point sets cover. -/
private theorem iUnion_range_pointsMap_ι_range_homOfLe_eq_univ {U : Subfunctor X} {K : Type*}
    {D : K → Subfunctor X} (hle : ∀ o, D o ≤ U)
    (h : ∀ z, ∃ o, pointsMap B S hS U.toFunctor U.ι z ∈
      Set.range (pointsMap B S hS (D o).toFunctor (D o).ι)) :
    (⋃ o, Set.range (pointsMap B S hS (Subfunctor.range (Subfunctor.homOfLe (hle o))).toFunctor
      (Subfunctor.range (Subfunctor.homOfLe (hle o))).ι)) = Set.univ := by
  refine Set.eq_univ_iff_forall.2 fun z ↦ ?_
  obtain ⟨o, q, hq⟩ := h z
  refine Set.mem_iUnion.2 ⟨o, ?_⟩
  rw [range_pointsMap_ι_range B S hS (Subfunctor.homOfLe (hle o))]
  refine ⟨q, pointsMap_injective_of_mono B S hS U.ι ?_⟩
  rwa [← pointsMap_comp_apply B S hS (Subfunctor.homOfLe (hle o)) U.ι q, Subfunctor.homOfLe_ι]

/-- **Stacks 0EMR.** Let `X` be a reduced algebraic space over `S` and let `Y` be an algebraic
space separated over `S`. A rational map from `X` to `Y` is represented by exactly one morphism
on the open subspace of `X` whose point set is its domain of definition. -/
@[stacks 0EMR, ega "I 7.2.2"]
theorem existsUnique_hom_of_eq_domainOfDefinition
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hYsep : IsSeparatedOver B S hS Y)
    (φ : RationalMap B S hS hX Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUdom : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      RationalMap.domainOfDefinition B S hS φ) :
    ∃! f : U.toFunctor ⟶ Y, ∃ hUd : IsDenseOpenSubspace B S hS hX U,
      PartialMap.toRationalMap B S hS ⟨U, hUd, f⟩ = φ := by
  have hle := domain_le_of_eq_domainOfDefinition B S hS hX φ U hU hUdom
  have hUd := isDenseOpenSubspace_of_eq_domainOfDefinition B S hS hX φ U hU hUdom
  obtain ⟨g₀, hg₀⟩ := RationalMap.exists_rep B S hS φ
  obtain ⟨K₀, γ, hγ, hγmem⟩ := exists_rep_cover_of_eq_domainOfDefinition B S hS hX φ U hU hUdom
  set rep : Option K₀ → PartialMap B S hS hX Y := fun o ↦ o.elim g₀ γ
  have hrep : ∀ o, (rep o).toRationalMap B S hS = φ := by
    rintro (_ | y)
    · exact hg₀
    · exact hγ y
  set E : Option K₀ → Subfunctor U.toFunctor :=
    fun o ↦ Subfunctor.range (Subfunctor.homOfLe (hle (rep o) (hrep o))) with hEdef
  have hcover : (⋃ o, Set.range (pointsMap B S hS (E o).toFunctor (E o).ι)) = Set.univ :=
    iUnion_range_pointsMap_ι_range_homOfLe_eq_univ B S hS (fun o ↦ hle (rep o) (hrep o))
      fun z ↦ (hγmem z).elim fun y hy ↦ ⟨some y, hy⟩
  set V : Subfunctor U.toFunctor := ⨆ o, E o with hVdef
  have hVtop : Subfunctor.sheafify (BigFppfOver.topology B S hS) V = ⊤ :=
    sheafify_iSup_eq_top_of_iUnion_range_eq_univ B S hS hU E
      (fun o ↦ isOpenSubspace_of_le B S hS _ U (rep o).dense_open_domain.1 _) hcover
  have hmemV : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : (V.toFunctor.obj T : Type u)),
      ∃ o, ∃ c : ((rep o).domain.obj T : Type u),
        (c : X.obj T) = ((x : (U.toFunctor.obj T : Type u)) : X.obj T) := by
    rintro T ⟨s, hs⟩
    rw [hVdef, Subfunctor.iSup_obj] at hs
    obtain ⟨o, hmem⟩ := Set.mem_iUnion.1 hs
    rw [hEdef] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨o, c, congrArg (fun z : (U.toFunctor.obj T : Type u) ↦ (z : X.obj T)) hc⟩
  obtain ⟨k, hk⟩ := exists_hom_of_forall_exists_rep B S hS hX hY hXred hYsep rep hrep V hmemV
  obtain ⟨f₁, hfk⟩ := exists_ι_comp_eq_of_sheafify_eq_top hVtop
    ((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) Y).1 hY.isSheaf) k
  have hrepf₁ : PartialMap.toRationalMap B S hS
      (⟨U, hUd, f₁⟩ : PartialMap B S hS hX Y) = φ := by
    rw [← hg₀]
    refine (PartialMap.toRationalMap_eq_iff B S hS).2
      ⟨g₀.domain, g₀.dense_open_domain, hle g₀ hg₀, le_rfl, ?_⟩
    ext T d
    have hd := hle g₀ hg₀ T d.2
    have hdV : (⟨(d : X.obj T), hd⟩ : (U.toFunctor.obj T : Type u)) ∈ V.obj T := by
      rw [hVdef, Subfunctor.iSup_obj]
      refine Set.mem_iUnion.2 ⟨none, ?_⟩
      rw [hEdef]
      exact ⟨d, rfl⟩
    calc f₁.app T ⟨(d : X.obj T), hd⟩
        = (V.ι ≫ f₁).app T ⟨⟨(d : X.obj T), hd⟩, hdV⟩ := rfl
      _ = k.app T ⟨⟨(d : X.obj T), hd⟩, hdV⟩ := by rw [hfk]
      _ = g₀.hom.app T d := hk T ⟨⟨(d : X.obj T), hd⟩, hdV⟩ none d rfl
  exact ⟨f₁, ⟨hUd, hrepf₁⟩, fun f' ⟨hUd', hrep'⟩ ↦
    hom_eq_of_toRationalMap_eq B S hS hX hY hXred hYsep hUd' hUd f' f₁
      (hrep'.trans hrepf₁.symm)⟩

end AlgebraicGeometry.Space

end
