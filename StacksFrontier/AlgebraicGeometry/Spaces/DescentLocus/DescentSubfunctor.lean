module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.DescendsAlong
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratumExistence
public import StacksFrontier.AlgebraicGeometry.Quot.StructureSheafMapIsoBaseChange

/-!
# The subfunctor of points at which the descent condition of Stacks 0D23 holds

Let `f : X ⟶ Y` be a morphism of algebraic spaces such that the structure map
`𝒪_{Y'} ⟶ f'_*𝒪_{X'}` of every base change `f' : X ×_Y Y' ⟶ Y'` is an isomorphism, and let `E`
be an `𝒪_X`-module. The descent condition `AlgebraicGeometry.Space.HasDescentAt f E g` is stable
under precomposition and étale local on the source of `g`. Hence the points `y : T ⟶ Y` at which
it holds form a subfunctor of `Y` which is étale local on the source, and a morphism `g : Y' ⟶ Y`
factors through that subfunctor exactly when the descent condition holds at `g`.

## Main definitions

* `AlgebraicGeometry.Space.DescentStratum.descentSubfunctor`

## Main results

* `AlgebraicGeometry.Space.DescentStratum.hasDescentAt_comp_iff`: the descent condition at
  `h ≫ q` is the descent condition at `h` for the base change of `f` along `q`.
* `AlgebraicGeometry.Space.DescentStratum.HasDescentAt.comp`: stability under precomposition.
* `AlgebraicGeometry.Space.DescentStratum.hasDescentAt_of_forall_chart`: étale locality.
* `AlgebraicGeometry.Space.DescentStratum.isEtaleLocalOnSource_descentSubfunctor`
* `AlgebraicGeometry.Space.DescentStratum.exists_lift_descentSubfunctor_iff`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.DescentStratum

open BottomRankLocus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (E : Modules.{u, u} B S hS X.1 X.2)

/-- **The descent condition along a composite is the descent condition for the base change.**
For `q : Y₀ ⟶ Y` and `h : T ⟶ Y₀`, the descent condition for `f` and `E` at `h ≫ q` is the descent
condition at `h` for the base change `f₀ : X ×_Y Y₀ ⟶ Y₀` of `f` and the pullback of `E` to
`X ×_Y Y₀`: the two fibre products `(X ×_Y Y₀) ×_{Y₀} T` and `X ×_Y T` agree. -/
theorem hasDescentAt_comp_iff {Y₀ T : AlgebraicSpaces B S hS} (q : Y₀ ⟶ Y) (h : T ⟶ Y₀) :
    HasDescentAt (pullback.snd f q) ((modulePullback B S hS (pullback.fst f q)).obj E) h ↔
      HasDescentAt f E (h ≫ q) := by
  let e := pullbackLeftPullbackSndIso f q h
  have h₁ : pullback.snd (pullback.snd f q) h = e.hom ≫ pullback.snd f (h ≫ q) :=
    (pullbackLeftPullbackSndIso_hom_snd f q h).symm
  have h₂ : pullback.fst (pullback.snd f q) h ≫ pullback.fst f q =
      e.hom ≫ pullback.fst f (h ≫ q) :=
    (pullbackLeftPullbackSndIso_hom_fst f q h).symm
  let c : (modulePullback B S hS (pullback.fst (pullback.snd f q) h)).obj
      ((modulePullback B S hS (pullback.fst f q)).obj E) ≅
      (modulePullback B S hS e.hom).obj
        ((modulePullback B S hS (pullback.fst f (h ≫ q))).obj E) :=
    (modulePullbackCompIso B S hS _ _).app E ≪≫
      eqToIso (congrArg (fun k => (modulePullback B S hS k).obj E) h₂) ≪≫
      ((modulePullbackCompIso B S hS _ _).app E).symm
  rw [hasDescentAt_iff_descendsAlong, hasDescentAt_iff_descendsAlong,
    ← descendsAlong_comp_iff e, h₁]
  exact ⟨fun hd => hd.of_iso c, fun hd => hd.of_iso c.symm⟩

/-- **The descent condition is stable under precomposition.** -/
theorem HasDescentAt.comp {Y' T : AlgebraicSpaces B S hS} {g : Y' ⟶ Y}
    (hg : HasDescentAt f E g) (t : T ⟶ Y') : HasDescentAt f E (t ≫ g) :=
  (hasDescentAt_comp_iff f E g t).1 (DescendsAlong.pullback hg t)

/-- **The hypothesis of Stacks 0D23 passes to base changes**: if the structure map of every base
change of `f` is an isomorphism, the same holds for every base change of `f₀ = X ×_Y Y₀ ⟶ Y₀`. -/
theorem isIso_structureSharp_snd_snd {Y₀ T : AlgebraicSpaces B S hS}
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    (q : Y₀ ⟶ Y) (h : T ⟶ Y₀) :
    IsIso (structureSharp B S hS (pullback.snd (pullback.snd f q) h)) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd f q h, isIso_structureSharp_comp_iff]
  exact hiso _

/-- **The descent condition is étale local on the source.** If every point of `Y'` lies in the
image of an étale chart `V` such that the descent condition holds at `V ⟶ Y' ⟶ Y`, it holds at
`g : Y' ⟶ Y`. -/
theorem hasDescentAt_of_forall_chart
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (h : ∀ y : points B S hS Y'.1, ∃ V : SmallEtale B S hS Y'.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
        HasDescentAt f E (chartToSpace B S hS Y' V ≫ g)) :
    HasDescentAt f E g := by
  rw [hasDescentAt_iff_descendsAlong]
  refine descendsAlong_of_forall_chart _ (hiso g) _ fun y => ?_
  obtain ⟨V, hV, hd⟩ := h y
  exact ⟨V, hV, isIso_structureSharp_snd_snd f hiso g _,
    (hasDescentAt_comp_iff f E g _).2 hd⟩

end

/-! ### The descent subfunctor -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (E : Modules.{u, u} B S hS X.1 X.2)

/-- **The candidate locus of Stacks 0D23.** The subfunctor of `Y` of the points `y : h_T ⟶ Y` at
which the descent condition holds. -/
def descentSubfunctor : Subfunctor Y.1 where
  obj U := {y | HasDescentAt f E (sectionMap U.unop y)}
  map {U V} i y hy := by
    change HasDescentAt f E (sectionMap V.unop (Y.1.map i.unop.op y))
    rw [sectionMap_map]
    exact HasDescentAt.comp f E hy _

/-- **The candidate locus is étale local on the source.** -/
theorem isEtaleLocalOnSource_descentSubfunctor
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g))) :
    IsEtaleLocalOnSource (descentSubfunctor f E) := by
  intro T x hx
  change HasDescentAt f E (sectionMap T x)
  refine hasDescentAt_of_forall_chart f E hiso _ fun y => ?_
  obtain ⟨W, hW, hmem⟩ := hx y
  refine ⟨W, hW, ?_⟩
  have h : HasDescentAt f E (sectionMap W.1.left (Y.1.map (yonedaEquiv W.1.hom).op x)) := hmem
  rw [sectionMap_map] at h
  have e : chartToSpace B S hS (representedAlgebraicSpace B S hS T) W =
      representedSpaceMap B S hS (yonedaEquiv W.1.hom) :=
    InducedCategory.hom_ext (yoneda_map_yonedaEquiv W.1.hom).symm
  rwa [e]

/-- **A morphism factors through the candidate locus exactly when the descent condition holds
at it.** -/
theorem exists_lift_descentSubfunctor_iff
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    (∃ g' : Y'.1 ⟶ (descentSubfunctor f E).toFunctor, g' ≫ (descentSubfunctor f E).ι = g.hom) ↔
      HasDescentAt f E g := by
  constructor
  · rintro ⟨g', hg'⟩
    refine hasDescentAt_of_forall_chart f E hiso g fun y => ?_
    obtain ⟨V, hV⟩ := exists_smallEtale_mem_range B S hS Y'.2 y
    refine ⟨V, hV, ?_⟩
    have hx : HasDescentAt f E (sectionMap V.1.left (g'.app _ (yonedaEquiv V.1.hom)).1) :=
      (g'.app _ (yonedaEquiv V.1.hom)).2
    have heq : (g'.app _ (yonedaEquiv V.1.hom)).1 = g.hom.app _ (yonedaEquiv V.1.hom) := by
      rw [← hg']
      rfl
    rwa [heq, sectionMap_app, sectionMap_yonedaEquiv] at hx
  · intro h
    refine ⟨Subfunctor.lift g.hom ?_, Subfunctor.lift_ι _ _⟩
    rintro U _ ⟨y, rfl⟩
    change HasDescentAt f E (sectionMap U.unop (g.hom.app U y))
    rw [sectionMap_app]
    exact HasDescentAt.comp f E h _

/-- A morphism factors through the candidate locus, read as an algebraic space, exactly when the
descent condition holds at it. -/
theorem exists_comp_homMk_ι_descentSubfunctor_iff
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g)))
    (hZ : IsAlgebraicSpace B S hS (descentSubfunctor f E).toFunctor)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    (∃ h : Y' ⟶ ⟨_, hZ⟩, h ≫ ObjectProperty.homMk (descentSubfunctor f E).ι = g) ↔
      HasDescentAt f E g := by
  rw [← exists_lift_descentSubfunctor_iff f E hiso g]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.hom, rfl⟩
  · rintro ⟨h, hh⟩
    exact ⟨ObjectProperty.homMk h, InducedCategory.hom_ext hh⟩

end AlgebraicGeometry.Space.DescentStratum

end
