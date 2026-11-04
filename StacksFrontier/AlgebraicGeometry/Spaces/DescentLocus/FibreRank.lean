module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.DescentSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.ClopenGlobalFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Ranks along a morphism with invertible structure maps

Let `f : X ⟶ Y` be a morphism of algebraic spaces such that the structure map of every base
change of `f` is an isomorphism, and `E` a finite locally free `𝒪_X`-module. This file collects
the statements about ranks used by the proof of Stacks 0D23.

* `|f'|` is surjective for every base change `f'` of `f`: over a field-valued point `Spec k ⟶ Y'`
  the base change has the nonzero ring `k` of global functions, hence a point.
* The rank of `E` is constant on the fibres of `|f|` (Stacks 0D23,
  `AlgebraicGeometry.Space.DescentStratum.mem_rankLocus_iff_of_pointsMap_eq`), so the points of
  `|Y|` over which `E` has rank `r` form an open set `rankFibreLocus f E r` (`|f|` being closed),
  and every point of `|Y|` lies in one of them. Over `rankFibreLocus f E r` the pullback of `E`
  has rank `r`.
* If the descent condition holds at `g : Y' ⟶ Y` and `|Y'|` lands in `rankFibreLocus f E r`,
  then `f'_*((g')^*E)` is finite locally free of rank `r`.

These are private, unregistered helpers for Stacks 0D23.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.surjective_pointsMap_snd`
* `AlgebraicGeometry.Space.DescentStratum.isOpen_rankFibreLocus`
* `AlgebraicGeometry.Space.DescentStratum.exists_mem_rankFibreLocus`
* `AlgebraicGeometry.Space.DescentStratum.isFiniteLocallyFreeOfIntRank_fst_of_range_subset`
* `AlgebraicGeometry.Space.DescentStratum.isFiniteLocallyFreeOfIntRank_pushforward_of_hasDescentAt`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.DescentStratum

open BottomRankLocus

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Ranks of modules -/

/-- Finite local freeness of a natural rank, in the integer form, is the rank form of the ringed
site. -/
theorem isFiniteLocallyFreeOfIntRank_iff_ringedSite {Y : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS Y.1 Y.2) (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank M (r : ℤ) ↔
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r :=
  (SheafOfModules.isFiniteLocallyFreeOfIntRank_natCast_iff _ r).trans
    (RingedSite.isFiniteLocallyFreeOfRank_iff_sheafOfModules _ _ r).symm

/-- A module finite locally free of rank `r` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank {Y : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Y.1 Y.2} {r : ℕ}
    (h : SheafOfModules.IsFiniteLocallyFreeOfIntRank M (r : ℤ)) :
    SheafOfModules.IsFiniteLocallyFree M := by
  have := (SheafOfModules.isFiniteLocallyFreeOfIntRank_natCast_iff _ r).1 h
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r

/-- **The rank of a pullback is read on points**: for a finite locally free `M` on `Y` and
`a : X ⟶ Y`, the pullback `a^*M` has rank `r` exactly when `|a|` lands in the rank locus of `r`
of `M`. -/
theorem isFiniteLocallyFreeOfIntRank_modulePullback_iff {X Y : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsFiniteLocallyFree M)
    (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank ((modulePullback B S hS a).obj M) (r : ℤ) ↔
      Set.range (pointsMap B S hS X.1 a.hom) ⊆ rankLocus M r := by
  rw [isFiniteLocallyFreeOfIntRank_iff_ringedSite]
  exact isFiniteLocallyFreeOfRank_modulePullback_iff a
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree M hM) r

/-- **The pullback of a module of rank `r` has rank `r`.** -/
theorem isFiniteLocallyFreeOfIntRank_modulePullback {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {r : ℕ}
    (hM : SheafOfModules.IsFiniteLocallyFreeOfIntRank M (r : ℤ)) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank ((modulePullback B S hS a).obj M) (r : ℤ) := by
  refine (isFiniteLocallyFreeOfIntRank_modulePullback_iff a
    (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hM) r).2 ?_
  rintro _ ⟨x, rfl⟩
  exact mem_rankLocus_of_isFiniteLocallyFreeOfRank
    ((isFiniteLocallyFreeOfIntRank_iff_ringedSite M r).1 hM) _

/-- **A rank is detected after pullback along a morphism surjective on points.** -/
theorem isFiniteLocallyFreeOfIntRank_of_modulePullback {X Y : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) (ha : Function.Surjective (pointsMap B S hS X.1 a.hom))
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsFiniteLocallyFree M) {r : ℕ}
    (h : SheafOfModules.IsFiniteLocallyFreeOfIntRank ((modulePullback B S hS a).obj M) (r : ℤ)) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank M (r : ℤ) := by
  have h₁ := (isFiniteLocallyFreeOfIntRank_modulePullback_iff a hM r).1 h
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (𝟙 Y)).obj M) (r : ℤ) := by
    refine (isFiniteLocallyFreeOfIntRank_modulePullback_iff (𝟙 Y) hM r).2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := ha y
    have : (𝟙 Y : Y ⟶ Y).hom = 𝟙 Y.1 := rfl
    rw [this, pointsMap_id]
    exact h₁ ⟨x, rfl⟩
  exact isFiniteLocallyFreeOfIntRank_of_iso B S hS ((modulePullbackIdIso B S hS Y).app M) h₂

/-! ### Surjectivity -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The base changes of `f` are surjective on points.** Over a field-valued point
`s : Spec k ⟶ Y'` the structure map of the base change of `f` along `s ≫ g` is an isomorphism, so
its ring of global functions is `k`, which is not zero; hence that base change has a point, and
its image in `X ×_Y Y'` lies over the point of `s`. -/
theorem surjective_pointsMap_snd
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    Function.Surjective (pointsMap B S hS (pullback f g).1 (pullback.snd f g).hom) := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  let T := p.siteObject
  let s : representedAlgebraicSpace B S hS T ⟶ Y' := sectionMap T p.value
  have := isIso_fSharp_of_isIso_structureSharp _ (hiso (s ≫ g))
  have hb := bijective_globalFunctionsMap_of_isIso_fSharp (pullback.snd f (s ≫ g))
  obtain ⟨t⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj T) :=
    inferInstanceAs (Nonempty (PrimeSpectrum p.carrier))
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    (((BigFppfOver.toScheme B S hS).obj T).presheaf.germ ⊤ t trivial).hom.domain_nontrivial
  have : Nontrivial (globalFunctions B S hS (yoneda.obj T)) :=
    (reprGlobalFunctionsEquiv B S hS T).toEquiv.nontrivial
  have : Nontrivial (globalFunctions B S hS (pullback f (s ≫ g)).1) :=
    ⟨⟨_, _, fun h => zero_ne_one (hb.1 ((map_zero _).trans (h.trans (map_one _).symm)))⟩⟩
  obtain ⟨w⟩ := nonempty_points_of_nontrivial_globalFunctions (F := (pullback f (s ≫ g)).1)
  let φ : pullback f (s ≫ g) ⟶ pullback f g :=
    pullback.lift (pullback.fst f (s ≫ g)) (pullback.snd f (s ≫ g) ≫ s)
      (by rw [pullback.condition, Category.assoc])
  refine ⟨pointsMap B S hS _ φ.hom w, ?_⟩
  have hφ : φ.hom ≫ (pullback.snd f g).hom = (pullback.snd f (s ≫ g)).hom ≫ s.hom :=
    congrArg (·.hom) (pullback.lift_snd _ _ _ : φ ≫ pullback.snd f g = _)
  rw [← pointsMap_comp_apply, hφ, pointsMap_comp_apply]
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum p.carrier))
  rw [show pointsMap B S hS _ (pullback.snd f (s ≫ g)).hom w =
      (p.tautologicalPoint B S hS Y'.1).class B S hS (yoneda.obj p.siteObject) from
    injective_pointsToScheme B S hS T (Subsingleton.elim _ _)]
  exact pointsMap_fieldMorphism_tautologicalPoint B S hS Y'.1 p

/-! ### The rank of `E` over the points of `Y` -/

/-- **The points of `|Y|` over which `E` has rank `r`.** -/
def rankFibreLocus (E : Modules.{u, u} B S hS X.1 X.2) (r : ℕ) : Set (points B S hS Y.1) :=
  {y | ∀ x, pointsMap B S hS X.1 f.hom x = y → x ∈ rankLocus E r}

/-- **The locus over which `E` has rank `r` is open**, `|f|` being closed. -/
theorem isOpen_rankFibreLocus (hf : UniversallyClosed B S hS f.hom)
    (E : Modules.{u, u} B S hS X.1 X.2) (r : ℕ) : IsOpen (rankFibreLocus f E r) := by
  have hclosed : IsClosedMap (pointsMap B S hS X.1 f.hom) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS f.hom (hf Y.1 Y.2 (𝟙 Y.1))
  have e : rankFibreLocus f E r = (pointsMap B S hS X.1 f.hom '' (rankLocus E r)ᶜ)ᶜ := by
    ext y
    simp only [rankFibreLocus, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists,
      not_and]
    exact ⟨fun h x hx hxy => hx (h x hxy), fun h x hxy => by_contra fun hx => h x hx hxy⟩
  rw [e]
  exact (hclosed _ (isOpen_rankLocus E r).isClosed_compl).isOpen_compl

/-- **Every point of `|Y|` lies over a single rank of `E`.** -/
theorem exists_mem_rankFibreLocus
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    {E : Modules.{u, u} B S hS X.1 X.2} (hE : SheafOfModules.IsFiniteLocallyFree E)
    (y : points B S hS Y.1) : ∃ r, y ∈ rankFibreLocus f E r := by
  have hE' : SheafOfModules.IsFiniteLocallyFreeOnSite E :=
    Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree E hE
  by_cases hy : ∃ x, pointsMap B S hS X.1 f.hom x = y
  · obtain ⟨x₀, hx₀⟩ := hy
    obtain ⟨r, hr⟩ := exists_mem_rankLocus hE' x₀
    exact ⟨r, fun x hx =>
      (mem_rankLocus_iff_of_pointsMap_eq f hiso hE' r (hx₀.trans hx.symm)).1 hr⟩
  · exact ⟨0, fun x hx => (hy ⟨x, hx⟩).elim⟩

/-- **Over the rank `r` locus the pullback of `E` has rank `r`.** -/
theorem isFiniteLocallyFreeOfIntRank_fst_of_range_subset
    {E : Modules.{u, u} B S hS X.1 X.2} (hE : SheafOfModules.IsFiniteLocallyFree E) {r : ℕ}
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (hg : Set.range (pointsMap B S hS Y'.1 g.hom) ⊆ rankFibreLocus f E r) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (pullback.fst f g)).obj E) (r : ℤ) := by
  refine (isFiniteLocallyFreeOfIntRank_modulePullback_iff _ hE r).2 ?_
  rintro _ ⟨w, rfl⟩
  have hw : (pullback.fst f g).hom ≫ f.hom = (pullback.snd f g).hom ≫ g.hom :=
    congrArg (fun m => m.hom) (pullback.condition (f := f) (g := g))
  refine hg ⟨pointsMap B S hS _ (pullback.snd f g).hom w, rfl⟩ _ ?_
  rw [← pointsMap_comp_apply, hw, pointsMap_comp_apply]

/-- **The direct image of `E'` is finite locally free of rank `r` when `E` descends.** If the
descent condition holds at `g` and `|Y'|` lands in the rank `r` locus, then `E' = (g')^*E` has
rank `r`, the module `N` with `(f')^*N ≅ E'` has rank `r` because `|f'|` is surjective, and
`f'_*E' ≅ N`. -/
theorem isFiniteLocallyFreeOfIntRank_pushforward_of_hasDescentAt
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    {E : Modules.{u, u} B S hS X.1 X.2} (hE : SheafOfModules.IsFiniteLocallyFree E) {r : ℕ}
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (hg : Set.range (pointsMap B S hS Y'.1 g.hom) ⊆ rankFibreLocus f E r)
    (hd : HasDescentAt f E g) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS (pullback.snd f g)).obj
        ((modulePullback B S hS (pullback.fst f g)).obj E)) (r : ℤ) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hd
  have h₁ := isFiniteLocallyFreeOfIntRank_of_iso B S hS e.symm
    (isFiniteLocallyFreeOfIntRank_fst_of_range_subset f hE g hg)
  have h₂ := isFiniteLocallyFreeOfIntRank_of_modulePullback _ (surjective_pointsMap_snd f hiso g)
    hN h₁
  obtain ⟨-, ⟨e'⟩⟩ := isFiniteLocallyFree_modulePushforward_of_iso_modulePullback _ (hiso g) N hN
    _ e.symm
  exact isFiniteLocallyFreeOfIntRank_of_iso B S hS e'.symm h₂

end AlgebraicGeometry.Space.DescentStratum

end
