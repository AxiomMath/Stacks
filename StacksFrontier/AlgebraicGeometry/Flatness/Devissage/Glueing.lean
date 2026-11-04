module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleFibreSupportDimension
public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.BaseChangeAt
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.SmoothFibreIrreducibleOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Normal

/-!
# Glueing a one-step dévissage across elementary étale neighbourhoods

Let `(Z, Y, i, π, G, z, y)` be a one-step dévissage of `F/X/S` at a point `x` (Tag 05H5), and let
`(Y', y') → (Y, y)` and `(S', s') → (S, s)` be elementary étale neighbourhoods fitting into a
commutative square over `Y → S`. Then, after a further elementary étale neighbourhood
`(S'', s'') → (S', s')`, there are an affine open `Y'' ⊆ Y' ×_{S'} S''` and an elementary étale
neighbourhood `(X'', x'') → (X, x)` such that `Z'' = Z ×_Y Y''` together with the pullback of `G`
is a one-step dévissage at `x''` of the pullback of `F` to `X''`.

That is Stacks 05HE. It is the step which makes a dévissage of `F/X/S` propagate along the
elementary étale neighbourhoods produced by Tag 057K, and it is one of the two inputs to Tag
05HR.

## Main results

* `AlgebraicGeometry.smooth_of_etale_square`: a morphism filling a commutative square between two
  étale morphisms and a smooth one is itself smooth.
* `AlgebraicGeometry.exists_oneStepDevissageAt_of_etaleNeighborhood` is Stacks 05HE.

## Implementation notes

The construction is the one in the source. First `S''` is produced: the residue field extension
`κ(s) ⊆ κ(y)` of the dévissage is purely transcendental, hence `κ(s)` is algebraically closed in
`κ(y)` (Tag 037I), and both residue fields are unchanged by the two elementary neighbourhoods, so
`κ(s')` is algebraically closed in `κ(y')`. Shrinking `Y'` and `S'` to affine opens `V₀` and `U₀`
makes the comparison morphism `h₀ : V₀ ⟶ U₀` smooth of finite presentation between affines, and
its fibre through `y'` then has a geometrically irreducible open neighbourhood `T₀` of `y'`
(`AlgebraicGeometry.exists_geometricallyIrreducible_open_fibre_of_isAlgClosedIn`). Tag 057J
spreads `T₀` out: it gives the elementary étale `(S'', s'') → (U₀, s')` and a quasi-compact open
`O` of `V₀ ×_{U₀} S''` with geometrically integral fibres whose fibre over `s''` is `T₀`. An
affine open `O₁ ⊆ O` containing the distinguished point, over a principal affine open of `S''`
contained in the image of `O`, is the `Y''` of the statement.

Then `Z''` and `X''` are produced: Tag 05H7 base changes the whole dévissage along
`S'' → S`, Tag 05H8 records that the base change is again a dévissage at the unique point
over `x`, and the étale `O₁ → Y''_{S''}` is pulled back to the closed subscheme and lifted across
the closed immersion by Tag 057R, which is what produces `X''`. The remaining fields of the new
dévissage are then checked one at a time; the two numerical ones use that dimension of a support
and of a fibre are unchanged along an étale morphism
(`AlgebraicGeometry.exists_mem_supp_fiber_dimension_of_etale` and
`AlgebraicGeometry.topologicalKrullDim_fiber_comp_eq_of_etale`), and the module identification
uses the affine base-change isomorphism of Tag 02KG.

Points of the various fibre products are specified by
`AlgebraicGeometry.pullbackPointOfIsIsoResidueFieldMap`: at every stage one of the two residue
field extensions involved is trivial, so there is exactly one point over the pair of points
chosen, which is how the source speaks of "the point `(y', s'')`".

## References

* [Stacks Project, Tag 05HE](https://stacks.math.columbia.edu/tag/05HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### A smooth morphism filling a square of étale morphisms -/

/-- If a composite `r ≫ g` is étale and `g` is étale, then `r` is étale. -/
private theorem etale_of_comp_eq {A B C : Scheme.{u}} (r : A ⟶ B) (g : B ⟶ C) {k : A ⟶ C}
    (hk : r ≫ g = k) [Etale k] [Etale g] : Etale r := by
  subst hk
  exact Etale.of_comp r g

/-- A monomorphism `r` whose composite with an étale `g` is étale is an open immersion. -/
private theorem isOpenImmersion_of_mono_of_comp_eq_etale {A B C : Scheme.{u}} (r : A ⟶ B)
    (g : B ⟶ C) {k : A ⟶ C} (hk : r ≫ g = k) [Mono r] [Etale k] [Etale g] :
    IsOpenImmersion r := by
  have := etale_of_comp_eq r g hk
  exact IsOpenImmersion.of_flat_of_mono r

/-- A morphism `h` filling a commutative square `v ≫ g = h ≫ u` in which `v` and `u` are étale
and `g` is smooth is itself smooth: it factors as an open immersion into the base change of `g`
along `u`, which is smooth. -/
theorem smooth_of_etale_square
    {V Y U S : Scheme.{u}} (v : V ⟶ Y) (g : Y ⟶ S) (u : U ⟶ S)
    (h : V ⟶ U) [Etale v] [Smooth g] [Etale u]
    (hc : v ≫ g = h ≫ u) : Smooth h := by
  let k := v ≫ g
  let r : V ⟶ pullback u k := pullback.lift h (𝟙 V) (by simpa [k] using hc.symm)
  have hr : r ≫ pullback.snd u k = 𝟙 V := pullback.lift_snd _ _ _
  have : Mono r := (SplitMono.mk (pullback.snd u k) hr).mono
  have : IsOpenImmersion r := isOpenImmersion_of_mono_of_comp_eq_etale r (pullback.snd u k) hr
  have hfactor : h = r ≫ pullback.fst u k := (pullback.lift_fst _ _ _).symm
  have : Smooth k := by
    dsimp [k]
    infer_instance
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@Smooth) u := ⟨fun sq hk =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hk⟩
  have : Smooth (pullback.fst u k) := MorphismProperty.pullback_fst u k inferInstance
  have : Smooth r := by infer_instance
  rw [hfactor]
  infer_instance

/-! ### Transporting the data of a dévissage -/

/-- A purely transcendental residue field extension recorded by a one-step dévissage may be
transported along an equality of the base points. -/
private lemma purelyTranscendental_residueFieldCongr
    {Y S : Scheme.{u}} (g : Y ⟶ S) (y : Y) (s t : S)
    (hs : g y = s) (ht : g y = t) (hst : s = t)
    (h : letI : Algebra (S.residueField s) (Y.residueField y) :=
        ((S.residueFieldCongr hs).inv ≫ g.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (Y.residueField y)) :
    letI : Algebra (S.residueField t) (Y.residueField y) :=
      ((S.residueFieldCongr ht).inv ≫ g.residueFieldMap y).hom.toAlgebra
    PurelyTranscendental (S.residueField t) (Y.residueField y) := by
  cases hst
  exact h

/-- The purely transcendental residue field extension of a one-step dévissage at a point
transports to any dévissage heterogeneously equal to it over an equal base point. This is how the
conclusion of Tag 05H8, which identifies the base-changed dévissage only up to `HEq`, is used. -/
private theorem purelyTranscendental_of_heq {X S : Scheme.{u}} (g : X ⟶ S) (F : X.Modules)
    (x : X) [LocallyOfFiniteType g] [F.IsQuasicoherent] [F.IsFiniteType]
    (E : OneStepDevissageAt g F x) (t : S) (ht : g x = t) (C : OneStepDevissage g F t) (cy : C.Y)
    (hC : HEq E.toOneStepDevissage C) (hcy : HEq E.y cy) (hgy : C.g cy = t) :
    letI : Algebra (S.residueField t) (C.Y.residueField cy) :=
      ((S.residueFieldCongr hgy).inv ≫ C.g.residueFieldMap cy).hom.toAlgebra
    PurelyTranscendental (S.residueField t) (C.Y.residueField cy) := by
  cases ht
  obtain rfl := eq_of_heq hC
  obtain rfl := eq_of_heq hcy
  exact E.residueField_purelyTranscendental

/-- In a cartesian square over a morphism whose fibre over a point is a single point, the fibre
of the base change over a point lying above it is again a single point, provided the residue
field extension of the right-hand morphism there is trivial. -/
private theorem preimage_singleton_of_isPullback {Z Y Z' Y' : Scheme.{u}} {π : Z ⟶ Y}
    {pZ : Z' ⟶ Z} {π' : Z' ⟶ Y'} {pY : Y' ⟶ Y} (sq : IsPullback pZ π' π pY) (z : Z) (y : Y)
    (hfib : π ⁻¹' {y} = {z}) (z' : Z') (y' : Y') (hz : pZ z' = z) (hy : pY y' = y)
    (hπ : π' z' = y') (hiso : IsIso (pY.residueFieldMap y')) : π' ⁻¹' {y'} = {z'} := by
  have hw' : ∀ w : Z', π' w = y' → pZ w = z := by
    intro w hw
    have hsq := congrArg (fun k : Z' ⟶ Y => k w) sq.w
    have hval : π (pZ w) = pY (π' w) := by
      simpa only [Scheme.Hom.comp_apply] using hsq
    have hmem : pZ w ∈ π ⁻¹' {y} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hval, hw, hy]
    rwa [hfib] at hmem
  have hfst : ∀ w, pullback.fst π pY (sq.isoPullback.hom w) = pZ w := fun w => by
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_fst]
  have hsnd : ∀ w, pullback.snd π pY (sq.isoPullback.hom w) = π' w := fun w => by
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_snd]
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun hw => ?_, fun hw => by rwa [hw]⟩
  refine (Scheme.Hom.homeomorph sq.isoPullback.hom).injective ?_
  simp only [Scheme.Hom.homeomorph_apply]
  refine pullback_point_ext_of_isIso_residueFieldMap π pY _ _ ?_ ?_ ?_
  · rw [hfst, hfst, hw' w hw, hz]
  · rw [hsnd, hsnd, hw, hπ]
  · rwa [hsnd, hπ]

/-- Pure transcendence of a residue field extension is inherited by a morphism `k` factoring as
`u ≫ g`, provided `u` induces an isomorphism of residue fields at the point in question. -/
private theorem purelyTranscendental_of_isIso_residueFieldMap_comp {Y Y' S : Scheme.{u}}
    (g : Y ⟶ S) (u : Y' ⟶ Y) (k : Y' ⟶ S) (hk : u ≫ g = k) (y' : Y') (y : Y) (s : S)
    (hu : u y' = y) (hg : g y = s) (hks : k y' = s)
    (hiso : IsIso ((Y.residueFieldCongr hu).inv ≫ u.residueFieldMap y'))
    (hPT : letI : Algebra (S.residueField s) (Y.residueField y) :=
        ((S.residueFieldCongr hg).inv ≫ g.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (Y.residueField y)) :
    letI : Algebra (S.residueField s) (Y'.residueField y') :=
      ((S.residueFieldCongr hks).inv ≫ k.residueFieldMap y').hom.toAlgebra
    PurelyTranscendental (S.residueField s) (Y'.residueField y') := by
  have hug : (u ≫ g) y' = s := by rwa [hk]
  set K := S.residueField s
  set L := Y.residueField y
  set L' := Y'.residueField y'
  set φold : CommRingCat.of K ⟶ CommRingCat.of L :=
    (S.residueFieldCongr hg).inv ≫ g.residueFieldMap y with hφold
  set β : CommRingCat.of L ⟶ CommRingCat.of L' :=
    (Y.residueFieldCongr hu).inv ≫ u.residueFieldMap y' with hβ
  set φnew : CommRingCat.of K ⟶ CommRingCat.of L' :=
    (S.residueFieldCongr hks).inv ≫ k.residueFieldMap y' with hφnew
  have hnorm := residueFieldCongr_inv_residueFieldMap_comp u g y' y s hu hg hug
  have hnormEq := residueFieldCongr_inv_residueFieldMap_eq_of_eq hk y' s hug hks
  have hpath : φold ≫ β = φnew := by
    rw [hφold, hβ, hφnew, ← hnormEq, hnorm, Category.assoc]
  have : IsIso β := hiso
  let : Algebra K L := φold.hom.toAlgebra
  let : Algebra K L' := φnew.hom.toAlgebra
  let : PurelyTranscendental K L := hPT
  exact (AlgEquiv.ofRingEquiv (f := (asIso β).commRingCatIsoToRingEquiv)
    (fun a => congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of L' => q.hom a)
      hpath)).purelyTranscendental

/-- The two transports of pure transcendence needed by the `residueField_purelyTranscendental`
field of the glued dévissage, in one step: along a morphism `k` factoring as `u ≫ g` with `u`
inducing an isomorphism of residue fields, and then along an equality of the base points.

This is stated separately only so that the field of the dévissage built in
`AlgebraicGeometry.exists_oneStepDevissageAt_of_etaleNeighborhood` is a single application: the
proof has a very large local context there, and discharging the field in place makes the
definitional unfolding of the two `letI`-bound `Algebra` instances the dominant cost of the
whole declaration. -/
private theorem purelyTranscendental_comp_congr {Y Y' S : Scheme.{u}}
    (g : Y ⟶ S) (u : Y' ⟶ Y) (k : Y' ⟶ S) (hk : u ≫ g = k) (y' : Y') (y : Y) (s t : S)
    (hu : u y' = y) (hg : g y = s) (hks : k y' = s) (hst : s = t)
    (hiso : IsIso ((Y.residueFieldCongr hu).inv ≫ u.residueFieldMap y'))
    (hPT : letI : Algebra (S.residueField s) (Y.residueField y) :=
        ((S.residueFieldCongr hg).inv ≫ g.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (Y.residueField y)) :
    letI : Algebra (S.residueField t) (Y'.residueField y') :=
      ((S.residueFieldCongr (hks.trans hst)).inv ≫ k.residueFieldMap y').hom.toAlgebra
    PurelyTranscendental (S.residueField t) (Y'.residueField y') :=
  purelyTranscendental_residueFieldCongr k y' s t hks (hks.trans hst) hst
    (purelyTranscendental_of_isIso_residueFieldMap_comp g u k hk y' y s hu hg hks hiso hPT)

/-! ### Residue fields across the square of étale neighbourhoods -/

/-- The square of residue field extensions attached to the commutative square of a dévissage and
a compatible pair of étale neighbourhoods commutes. -/
private theorem residueFieldMap_etaleNeighborhood_square
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x)
    (U : EtaleNeighborhood S (f x))
    (V : EtaleNeighborhood D.toOneStepDevissage.Y D.y)
    (h : V.scheme ⟶ U.scheme)
    (hcomm : V.toBase ≫ D.toOneStepDevissage.g = h ≫ U.toBase)
    (hpoint : h V.point = U.point) :
    ((S.residueFieldCongr D.g_y).inv ≫
      D.toOneStepDevissage.g.residueFieldMap D.y) ≫
        EtaleNeighborhood.residueFieldMap V =
      EtaleNeighborhood.residueFieldMap U ≫
        (U.scheme.residueFieldCongr hpoint).inv ≫ h.residueFieldMap V.point := by
  have hleft : (V.toBase ≫ D.toOneStepDevissage.g) V.point = f x := by
    simp [V.map_point, D.g_y]
  have hright : (h ≫ U.toBase) V.point = f x := by
    simp [hpoint, U.map_point]
  have hR := residueFieldCongr_inv_residueFieldMap_comp h U.toBase
    V.point U.point (f x) hpoint U.map_point hright
  calc
    _ = (S.residueFieldCongr hleft).inv ≫
          (V.toBase ≫ D.toOneStepDevissage.g).residueFieldMap V.point :=
      (residueFieldCongr_inv_residueFieldMap_comp V.toBase D.toOneStepDevissage.g
        V.point D.y (f x) V.map_point D.g_y hleft).symm
    _ = (S.residueFieldCongr hright).inv ≫
          (h ≫ U.toBase).residueFieldMap V.point :=
      residueFieldCongr_inv_residueFieldMap_eq_of_eq hcomm V.point (f x) hleft hright
    _ = _ := by simpa [EtaleNeighborhood.residueFieldMap, Category.assoc] using hR

/-- Relative algebraic closedness of a field extension `α` transports along a commutative square of
field homomorphisms whose horizontal maps `β`, `γ` are isomorphisms. -/
private theorem isAlgClosedIn_of_isIso_square {K E K' E' : Type u} [Field K] [Field E] [Field K']
    [Field E'] {α : CommRingCat.of K ⟶ CommRingCat.of E}
    {β : CommRingCat.of E ⟶ CommRingCat.of E'}
    {γ : CommRingCat.of K ⟶ CommRingCat.of K'} {δ : CommRingCat.of K' ⟶ CommRingCat.of E'}
    (hβ : IsIso β) (hγ : IsIso γ) (hsq : α ≫ β = γ ≫ δ)
    (h : letI := α.hom.toAlgebra; IsAlgClosedIn K E) :
    letI := δ.hom.toAlgebra
    IsAlgClosedIn K' E' := by
  let := α.hom.toAlgebra
  let := δ.hom.toAlgebra
  have := hβ
  have := hγ
  exact IsAlgClosedIn.of_ringEquiv_square (asIso γ).commRingCatIsoToRingEquiv
    (asIso β).commRingCatIsoToRingEquiv
    (fun a => congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of E' => q.hom a) hsq) h

/-- Across a compatible pair of elementary étale neighbourhoods, the residue field of the base of
a one-step dévissage stays algebraically closed in the residue field of the smooth scheme: both
residue fields are unchanged, and the original extension is purely transcendental. -/
private theorem isAlgClosedIn_etaleNeighborhood_residueField
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x)
    (U : EtaleNeighborhood S (f x)) (hU : U.IsElementary)
    (V : EtaleNeighborhood D.toOneStepDevissage.Y D.y)
    (hV : V.IsElementary) (h : V.scheme ⟶ U.scheme)
    (hcomm : V.toBase ≫ D.toOneStepDevissage.g = h ≫ U.toBase)
    (hpoint : h V.point = U.point) :
    letI : Algebra (U.scheme.residueField U.point) (V.scheme.residueField V.point) :=
      (((U.scheme.residueFieldCongr hpoint).inv ≫ h.residueFieldMap V.point).hom.toAlgebra)
    IsAlgClosedIn (U.scheme.residueField U.point) (V.scheme.residueField V.point) := by
  let : Algebra (S.residueField (f x)) (D.toOneStepDevissage.Y.residueField D.y) :=
    ((S.residueFieldCongr D.g_y).inv ≫ D.toOneStepDevissage.g.residueFieldMap D.y).hom.toAlgebra
  let : PurelyTranscendental (S.residueField (f x)) (D.toOneStepDevissage.Y.residueField D.y) :=
    D.residueField_purelyTranscendental
  have hclosed : IsAlgClosedIn (S.residueField (f x)) (D.toOneStepDevissage.Y.residueField D.y) :=
    IsAlgClosedIn.of_purelyTranscendental _ _
  exact isAlgClosedIn_of_isIso_square hV hU
    (residueFieldMap_etaleNeighborhood_square f F x D U V h hcomm hpoint) hclosed


/-! ### Stacks 05HE -/


/-- The first half of the construction of Stacks 05HE: the elementary étale neighbourhood
`(S'', s'') → (S', s')` together with the affine open `Y'' ⊆ Y' ×_{S'} S''`, presented as an open
immersion of `Y''` into `Y' ×_{S'} S''`.

The neighbourhood is affine and elementary, `Y''` is affine, the morphism `Y'' ⟶ Y'` is étale and
induces an isomorphism of residue fields at the distinguished point, and the morphism
`Y'' ⟶ S''` is smooth with geometrically irreducible fibres. -/
private theorem exists_etaleShrinking_of_oneStepDevissageAt {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x) (U : EtaleNeighborhood S (f x)) (hU : U.IsElementary)
    (V : EtaleNeighborhood D.toOneStepDevissage.Y D.y) (hV : V.IsElementary)
    (h : V.scheme ⟶ U.scheme)
    (hcomm : V.toBase ≫ D.toOneStepDevissage.g = h ≫ U.toBase)
    (hpoint : h V.point = U.point) :
    ∃ (W : EtaleNeighborhood U.scheme U.point) (_ : W.IsElementary) (_ : IsAffine W.scheme)
      (P : Scheme.{u}) (p : P) (_ : IsAffine P) (a : P ⟶ V.scheme) (c : P ⟶ W.scheme)
      (_ : Etale a) (_ : Smooth c) (j : P ⟶ pullback h W.toBase) (_ : IsOpenImmersion j),
      GeometricallyIrreducible c ∧ a ≫ h = c ≫ W.toBase ∧ a p = V.point ∧ c p = W.point ∧
        IsIso (a.residueFieldMap p) ∧ j ≫ pullback.fst h W.toBase = a ∧
        j ≫ pullback.snd h W.toBase = c := by
  let : Smooth D.toOneStepDevissage.g := D.toOneStepDevissage.smooth
  let : Smooth V.toBase := by infer_instance
  let : Smooth U.toBase := by infer_instance
  let : Smooth h := smooth_of_etale_square V.toBase D.toOneStepDevissage.g U.toBase h hcomm
  have hclosed := isAlgClosedIn_etaleNeighborhood_residueField
    f F x D U hU V hV h hcomm hpoint
  obtain ⟨U₀, hU₀aff, hU₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : U.scheme.Opens)) (Set.mem_univ U.point)
  let pre : V.scheme.Opens := h ⁻¹ᵁ U₀
  have hvpre : V.point ∈ pre := by
    show h V.point ∈ U₀
    rwa [hpoint]
  obtain ⟨V₀, hV₀aff, hV₀, hV₀sub⟩ := exists_isAffineOpen_mem_and_subset (U := pre) hvpre
  have hV₀le : V₀ ≤ pre := hV₀sub
  let v₀ : V₀.toScheme := ⟨V.point, hV₀⟩
  let h₀ : V₀.toScheme ⟶ U₀.toScheme :=
    V.scheme.homOfLE hV₀le ≫ h ∣_ U₀
  let u₀ : U₀.toScheme := h₀ v₀
  have hvu : V₀.ι v₀ = V.point := rfl
  have hcomm₀ : h₀ ≫ U₀.ι = V₀.ι ≫ h := by
    calc
      h₀ ≫ U₀.ι = V.scheme.homOfLE hV₀le ≫
          ((h ∣_ U₀) ≫ U₀.ι) := by simp [h₀, Category.assoc]
      _ = V.scheme.homOfLE hV₀le ≫ (pre.ι ≫ h) := by
        rw [morphismRestrict_ι]
      _ = V₀.ι ≫ h := by
        rw [← Category.assoc, Scheme.homOfLE_ι]
  have hu : U₀.ι u₀ = U.point := by
    have hh := congrArg (fun g : V₀.toScheme ⟶ U.scheme => g v₀) hcomm₀
    simpa [Scheme.Hom.comp_apply, hpoint, hvu] using hh
  have : Smooth (h ∣_ U₀) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict h U₀).flip inferInstance
  have : IsOpenImmersion (V.scheme.homOfLE hV₀le) := inferInstance
  have : Smooth h₀ := by infer_instance
  have : IsAffine V₀.toScheme := hV₀aff
  have : IsAffine U₀.toScheme := hU₀aff
  have : IsAffineHom h₀ := isAffineHom_of_isAffine h₀
  have hhfp : AlgebraicGeometry.FinitePresentation h₀ :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hclosed₀ :
      let : Algebra (U₀.toScheme.residueField (h₀ v₀))
          (V₀.toScheme.residueField v₀) :=
        ((U₀.toScheme.residueFieldCongr rfl).inv ≫ h₀.residueFieldMap v₀).hom.toAlgebra
      IsAlgClosedIn (U₀.toScheme.residueField (h₀ v₀))
        (V₀.toScheme.residueField v₀) := by
    have hp₁ : (V₀.ι ≫ h) v₀ = U.point := by
      simpa [Scheme.Hom.comp_apply, hvu] using hpoint
    have hp₂ : (h₀ ≫ U₀.ι) v₀ = U.point := by rwa [hcomm₀]
    let α : U.scheme.residueField U.point ⟶ V.scheme.residueField V.point :=
      (U.scheme.residueFieldCongr hpoint).inv ≫ h.residueFieldMap V.point
    let β : V.scheme.residueField V.point ⟶ V₀.toScheme.residueField v₀ :=
      (V.scheme.residueFieldCongr hvu).inv ≫ V₀.ι.residueFieldMap v₀
    let γ : U.scheme.residueField U.point ⟶ U₀.toScheme.residueField (h₀ v₀) :=
      (U.scheme.residueFieldCongr hu).inv ≫ U₀.ι.residueFieldMap (h₀ v₀)
    let δ : U₀.toScheme.residueField (h₀ v₀) ⟶ V₀.toScheme.residueField v₀ :=
      (U₀.toScheme.residueFieldCongr rfl).inv ≫ h₀.residueFieldMap v₀
    have hβ : IsIso β := by
      dsimp [β]
      infer_instance
    have hγ : IsIso γ := by
      dsimp [γ]
      infer_instance
    let : Algebra (U.scheme.residueField U.point) (V.scheme.residueField V.point) :=
      α.hom.toAlgebra
    have hnorm₁ := residueFieldCongr_inv_residueFieldMap_comp V₀.ι h v₀ V.point U.point
      hvu hpoint hp₁
    have hnorm₂ := residueFieldCongr_inv_residueFieldMap_comp h₀ U₀.ι v₀ (h₀ v₀) U.point
      rfl hu hp₂
    have hnormEq := residueFieldCongr_inv_residueFieldMap_eq_of_eq hcomm₀.symm v₀ U.point hp₁ hp₂
    have hmap : α ≫ β = γ ≫ δ := by
      calc
        α ≫ β = (U.scheme.residueFieldCongr hp₁).inv ≫
            (V₀.ι ≫ h).residueFieldMap v₀ := by
          simpa [α, β, Category.assoc] using hnorm₁.symm
        _ = (U.scheme.residueFieldCongr hp₂).inv ≫
            (h₀ ≫ U₀.ι).residueFieldMap v₀ := hnormEq
        _ = γ ≫ δ := by
          dsimp [γ, δ]
          exact hnorm₂
    exact isAlgClosedIn_of_isIso_square hβ hγ hmap hclosed
  obtain ⟨T₀, hT₀v, hT₀geom⟩ :=
    exists_geometricallyIrreducible_open_fibre_of_isAlgClosedIn h₀ v₀ hclosed₀
  obtain ⟨W, hW, hWaff, O, hOqc, hOgeom, hOfiber⟩ :=
    exists_etaleNeighborhood_geometricallyIntegral h₀ u₀ T₀ hhfp h₀.isNormal_of_smooth
  let W' : EtaleNeighborhood U.scheme U.point :=
    { scheme := W.scheme
      point := W.point
      toBase := W.toBase ≫ U₀.ι
      map_point := by
        calc
          (W.toBase ≫ U₀.ι) W.point = U₀.ι (W.toBase W.point) := rfl
          _ = U₀.ι u₀ := congrArg U₀.ι W.map_point
          _ = U.point := hu }
  have hW' : W'.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_comp W.toBase U₀.ι W.point (W.isElementary_iff.1 hW) inferInstance
  let qPt : (pullback h₀ W.toBase : Scheme).carrier :=
    pullbackPointOfIsIsoResidueFieldMap h₀ W.toBase v₀ W.point u₀ rfl W.map_point hW
  have hqPtW : pullback.snd h₀ W.toBase qPt = W.point :=
    pullbackPointOfIsIsoResidueFieldMap_snd h₀ W.toBase v₀ W.point u₀ rfl W.map_point hW
  let qPtFiber : (pullback.snd h₀ W.toBase).fiber W.point :=
    ((pullback.snd h₀ W.toBase).fiberHomeo W.point).symm ⟨qPt, hqPtW⟩
  let qPtInFiber := (pullback.snd h₀ W.toBase).fiberι W.point qPtFiber
  have hqPtFiberι : qPtInFiber = qPt := by
    simp [qPtInFiber, qPtFiber]
  have hqPtInO : qPtInFiber ∈ O := by
    apply (hOfiber qPtFiber).2
    refine ⟨h₀.asFiber v₀, hT₀v, ?_⟩
    show h₀.fiberι u₀ (h₀.asFiber v₀) = pullback.fst h₀ W.toBase qPtInFiber
    calc
      h₀.fiberι u₀ (h₀.asFiber v₀) = v₀ := Scheme.Hom.fiberι_asFiber h₀ v₀
      _ = pullback.fst h₀ W.toBase qPtInFiber := by
        rw [hqPtFiberι]
        exact (pullbackPointOfIsIsoResidueFieldMap_fst h₀ W.toBase v₀ W.point u₀
          rfl W.map_point hW).symm
  obtain ⟨O₀, hO₀aff, hO₀, hO₀sub⟩ := exists_isAffineOpen_mem_and_subset (U := O) hqPtInO
  have hO₀le : O₀ ≤ O := hO₀sub
  let m : O₀.toScheme ⟶ W.scheme :=
    O₀.ι ≫ pullback.snd h₀ W.toBase
  have : Smooth (pullback.snd h₀ W.toBase) := by infer_instance
  have : Smooth O₀.ι := by infer_instance
  have : Smooth m := by infer_instance
  have : Flat m := by infer_instance
  have : LocallyOfFinitePresentation m := by infer_instance
  have : UniversallyOpen m := inferInstance
  let Wimage : W.scheme.Opens := ⟨Set.range m, m.isOpenMap.isOpen_range⟩
  let o₀ : O₀.toScheme := ⟨qPtInFiber, hO₀⟩
  have hmPoint : m o₀ = W.point := by
    show pullback.snd h₀ W.toBase (O₀.ι o₀) = W.point
    rw [show O₀.ι o₀ = qPtInFiber from rfl, hqPtFiberι]
    exact hqPtW
  have hWpoint : W.point ∈ Wimage := ⟨o₀, hmPoint⟩
  obtain ⟨a, haWimage, haWpoint⟩ :=
    (isAffineOpen_top W.scheme).exists_basicOpen_le
      (⟨W.point, hWpoint⟩ : Wimage) (by simp)
  let Wsmall : W.scheme.Opens := W.scheme.basicOpen a
  have hWsmallAffine : IsAffine Wsmall.toScheme := (isAffineOpen_top W.scheme).basicOpen a
  have hWsmallPoint : W.point ∈ Wsmall := haWpoint
  have : IsAffine O₀.toScheme := hO₀aff
  have : IsAffine W.scheme := hWaff
  have : IsAffineHom m := inferInstance
  let O₁ : O₀.toScheme.Opens := m ⁻¹ᵁ Wsmall
  have hO₁aff : IsAffine O₁.toScheme := ((isAffineOpen_top W.scheme).basicOpen a).preimage m
  let o₁ : O₁.toScheme := ⟨o₀, by change m o₀ ∈ Wsmall; rw [hmPoint]; exact hWsmallPoint⟩
  let Wnew : EtaleNeighborhood U.scheme U.point :=
    { scheme := Wsmall.toScheme
      point := ⟨W.point, hWsmallPoint⟩
      toBase := Wsmall.ι ≫ W'.toBase
      map_point := W'.map_point }
  have hWnew : Wnew.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff] at hW' ⊢
    exact isIso_residueFieldMap_comp Wsmall.ι W'.toBase _ inferInstance
      ((W'.toBase.isIso_residueFieldMap_congr rfl).mpr hW')
  let vPart : O₁.toScheme ⟶ V.scheme :=
    O₁.ι ≫ O₀.ι ≫ pullback.fst h₀ W.toBase ≫ V₀.ι
  let wPart : O₁.toScheme ⟶ Wsmall.toScheme := m ∣_ Wsmall
  have hwPart : wPart ≫ Wsmall.ι = O₁.ι ≫ m := by
    dsimp [wPart, O₁]
    rw [morphismRestrict_ι]
  have hvwPart : vPart ≫ h = wPart ≫ Wnew.toBase := by
    dsimp [vPart, Wnew]
    calc
      _ = O₁.ι ≫ O₀.ι ≫ pullback.fst h₀ W.toBase ≫
          (V₀.ι ≫ h) := by cat_disch
      _ = O₁.ι ≫ O₀.ι ≫ pullback.fst h₀ W.toBase ≫
          (h₀ ≫ U₀.ι) := by rw [hcomm₀.symm]
      _ = O₁.ι ≫ O₀.ι ≫
          (pullback.fst h₀ W.toBase ≫ h₀) ≫ U₀.ι := by cat_disch
      _ = O₁.ι ≫ O₀.ι ≫
          (pullback.snd h₀ W.toBase ≫ W.toBase) ≫ U₀.ι := by
        rw [pullback.condition]
      _ = O₁.ι ≫ O₀.ι ≫ pullback.snd h₀ W.toBase ≫ W.toBase ≫ U₀.ι := by
        cat_disch
      _ = O₁.ι ≫ m ≫ W'.toBase := by
        dsimp [m, W']
        cat_disch
      _ = (wPart ≫ Wsmall.ι) ≫ W'.toBase :=
        congrArg (fun q => q ≫ W'.toBase) hwPart.symm
      _ = wPart ≫ Wsmall.ι ≫ W'.toBase := by cat_disch
  let jRaw : O₁.toScheme ⟶ pullback h Wnew.toBase :=
    pullback.lift vPart wPart hvwPart
  have hjRaw_fst : jRaw ≫ pullback.fst h Wnew.toBase = vPart := pullback.lift_fst _ _ _
  have hjRaw_snd : jRaw ≫ pullback.snd h Wnew.toBase = wPart := pullback.lift_snd _ _ _
  have hO₁point : O₀.ι (O₁.ι o₁) = qPt := hqPtFiberι
  have hvPartPoint : vPart o₁ = V.point := by
    show V₀.ι (pullback.fst h₀ W.toBase (O₀.ι (O₁.ι o₁))) = V.point
    rw [hO₁point, pullbackPointOfIsIsoResidueFieldMap_fst h₀ W.toBase v₀ W.point u₀
      rfl W.map_point hW, hvu]
  have hwPartPoint : wPart o₁ = Wnew.point := by
    apply Subtype.ext
    have hh := congrArg (fun k : O₁.toScheme ⟶ W.scheme => k o₁) hwPart
    change Wsmall.ι (wPart o₁) = m o₀ at hh
    exact hh.trans hmPoint
  have hWraw₀ : IsIso (W.toBase.residueFieldMap W.point) := W.isElementary_iff.1 hW
  have hvPartIso : IsIso (vPart.residueFieldMap o₁) := by
    have h1 : IsIso (O₁.ι.residueFieldMap o₁) := by infer_instance
    have h2 : IsIso (O₀.ι.residueFieldMap (O₁.ι o₁)) := by infer_instance
    have hWraw_q : IsIso (W.toBase.residueFieldMap
        (pullback.snd h₀ W.toBase qPt)) := by
      rw [hqPtW]
      exact hWraw₀
    have h3 : IsIso ((pullback.fst h₀ W.toBase).residueFieldMap
        (O₀.ι (O₁.ι o₁))) := by
      rw [hO₁point]
      exact isIso_residueFieldMap_pullback_fst_of_right h₀ W.toBase qPt hWraw_q
    have h4 : IsIso (V₀.ι.residueFieldMap
        (pullback.fst h₀ W.toBase (O₀.ι (O₁.ι o₁)))) := by infer_instance
    have h₃₄ : IsIso ((pullback.fst h₀ W.toBase ≫ V₀.ι).residueFieldMap
        (O₀.ι (O₁.ι o₁))) :=
      isIso_residueFieldMap_comp (pullback.fst h₀ W.toBase) V₀.ι
        (O₀.ι (O₁.ι o₁)) h3 h4
    have h₂₃₄ : IsIso ((O₀.ι ≫ pullback.fst h₀ W.toBase ≫ V₀.ι).residueFieldMap
        (O₁.ι o₁)) :=
      isIso_residueFieldMap_comp O₀.ι
        (pullback.fst h₀ W.toBase ≫ V₀.ι) (O₁.ι o₁) h2 h₃₄
    exact isIso_residueFieldMap_comp O₁.ι
      (O₀.ι ≫ pullback.fst h₀ W.toBase ≫ V₀.ι) o₁ h1 h₂₃₄
  have hwgeom : GeometricallyIrreducible wPart := by
    let fullMap : O.toScheme ⟶ W.scheme := O.ι ≫ pullback.snd h₀ W.toBase
    let fullOpen : O.toScheme.Opens := fullMap ⁻¹ᵁ Wsmall
    let rO : O₀.toScheme ⟶ O.toScheme :=
      (pullback h₀ W.toBase).homOfLE hO₀le
    have hrO : rO ≫ fullMap = m := by
      dsimp [rO, fullMap, m]
      rw [← Category.assoc, Scheme.homOfLE_ι]
    let jO1 : O₁.toScheme ⟶ O.toScheme := O₁.ι ≫ rO
    have hsurj : Surjective wPart := by
      refine ⟨fun y => ?_⟩
      have hy : Wsmall.ι y ∈ Wimage := haWimage y.property
      change Wsmall.ι y ∈ Set.range m at hy
      obtain ⟨x, hx⟩ := Set.mem_range.mp hy
      have hxW : m x ∈ Wsmall := by rw [hx]; exact y.property
      let x' : O₁.toScheme := ⟨x, hxW⟩
      refine ⟨x', ?_⟩
      apply Wsmall.ι.injective
      have hc := congrArg (fun k : O₁.toScheme ⟶ W.scheme => k x') hwPart
      change Wsmall.ι (wPart x') = m (O₁.ι x') at hc
      rwa [show O₁.ι x' = x from rfl, hx] at hc
    have hrange : Set.range jO1 ⊆ Set.range fullOpen.ι := by
      rintro y ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      show fullMap (rO (O₁.ι x)) ∈ Wsmall
      rw [← Scheme.Hom.comp_apply, hrO]
      exact x.property
    let jO : O₁.toScheme ⟶ fullOpen.toScheme :=
      IsOpenImmersion.lift fullOpen.ι jO1 hrange
    have hjO : jO ≫ fullOpen.ι = jO1 :=
      IsOpenImmersion.lift_fac fullOpen.ι jO1 hrange
    have : IsOpenImmersion rO := by infer_instance
    have : IsOpenImmersion jO1 := by dsimp [jO1]; infer_instance
    have : IsOpenImmersion (jO ≫ fullOpen.ι) := by rw [hjO]; infer_instance
    have : IsOpenImmersion fullOpen.ι := by infer_instance
    have : IsOpenImmersion jO := IsOpenImmersion.of_comp jO fullOpen.ι
    let fFull : fullOpen.toScheme ⟶ Wsmall.toScheme := fullMap ∣_ Wsmall
    let : GeometricallyIntegral fullMap := hOgeom
    let : GeometricallyIntegral fFull := by
      dsimp [fFull, fullMap]
      infer_instance
    have hjFactor : jO ≫ fFull = wPart := by
      apply (cancel_mono Wsmall.ι).1
      calc
        jO ≫ fFull ≫ Wsmall.ι = jO ≫ fullOpen.ι ≫ fullMap :=
          congrArg (fun k => jO ≫ k) (morphismRestrict_ι fullMap Wsmall)
        _ = jO1 ≫ fullMap := by rw [← Category.assoc, hjO]
        _ = O₁.ι ≫ m := by
          show (O₁.ι ≫ rO) ≫ fullMap = O₁.ι ≫ m
          rw [Category.assoc, hrO]
        _ = wPart ≫ Wsmall.ι := hwPart.symm
    have : Surjective (jO ≫ fFull) := by
      rw [hjFactor]
      exact hsurj
    have hgi : GeometricallyIrreducible (jO ≫ fFull) := by infer_instance
    rwa [hjFactor] at hgi
  have hjOpen : IsOpenImmersion jRaw := by
    have : Mono jRaw := ⟨by
      intro T a c hac
      apply (cancel_mono O₁.ι).1
      apply (cancel_mono O₀.ι).1
      apply pullback.hom_ext
      · apply (cancel_mono V₀.ι).1
        have hv := congrArg (fun k => k ≫ pullback.fst h Wnew.toBase) hac
        simpa only [Category.assoc, hjRaw_fst] using hv
      · have hw : a ≫ wPart = c ≫ wPart := by
          simpa only [Category.assoc, hjRaw_snd] using
            congrArg (fun k => k ≫ pullback.snd h Wnew.toBase) hac
        have hw' := congrArg (fun k => k ≫ Wsmall.ι) hw
        simpa only [Category.assoc, hwPart, m] using hw'⟩
    have : Etale vPart := by dsimp [vPart]; infer_instance
    exact isOpenImmersion_of_mono_of_comp_eq_etale jRaw (pullback.fst h Wnew.toBase) hjRaw_fst
  have : Etale vPart := by dsimp [vPart]; infer_instance
  have : Smooth wPart := by dsimp [wPart]; infer_instance
  exact ⟨Wnew, hWnew, hWsmallAffine, O₁.toScheme, o₁, hO₁aff, vPart, wPart, inferInstance,
    inferInstance, jRaw, hjOpen, hwgeom, hvwPart, hvPartPoint, hwPartPoint, hvPartIso,
    hjRaw_fst, hjRaw_snd⟩

/-- **Stacks Project, Tag 05HE.** A one-step dévissage at a point can be pulled through a
compatible pair of elementary étale neighbourhoods of the base and of the smooth scheme, after a
further elementary étale localization of the base: the new smooth scheme is an open subscheme of
the base change of the given neighbourhood, the new closed subscheme is the base change of the
old one, and the new module is the pullback of the old one. -/
@[stacks 05HE]
theorem exists_oneStepDevissageAt_of_etaleNeighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x)
    (U : EtaleNeighborhood S (f x)) (hU : U.IsElementary)
    (V : EtaleNeighborhood D.toOneStepDevissage.Y D.y)
    (hV : V.IsElementary) (h : V.scheme ⟶ U.scheme)
    (hcomm : V.toBase ≫ D.toOneStepDevissage.g = h ≫ U.toBase)
    (hpoint : h V.point = U.point) :
    ∃ (W : EtaleNeighborhood U.scheme U.point)
      (_ : W.IsElementary)
      (A : EtaleNeighborhood X x) (_ : A.IsElementary)
      (b : A.scheme ⟶ W.scheme),
      b A.point = W.point ∧
      A.toBase ≫ f = b ≫ W.toBase ≫ U.toBase ∧
      ∃ (hl : LocallyOfFiniteType b)
        (hq : ((Scheme.Modules.pullback A.toBase).obj F).IsQuasicoherent)
        (ht : ((Scheme.Modules.pullback A.toBase).obj F).IsFiniteType),
        letI := hl
        letI := hq
        letI := ht
        ∃ (D' : OneStepDevissageAt b ((Scheme.Modules.pullback A.toBase).obj F) A.point)
          (j : D'.toOneStepDevissage.Y ⟶ pullback h W.toBase)
          (p : D'.toOneStepDevissage.Z ⟶ D.toOneStepDevissage.Z),
          IsOpenImmersion j ∧
          D'.toOneStepDevissage.g = j ≫ pullback.snd h W.toBase ∧
          (j ≫ pullback.fst h W.toBase) D'.y = V.point ∧
          p D'.z = D.z ∧
          D'.toOneStepDevissage.i ≫ A.toBase =
            p ≫ D.toOneStepDevissage.i ∧
          IsPullback p D'.toOneStepDevissage.i D.toOneStepDevissage.i
            A.toBase ∧
          IsPullback p D'.toOneStepDevissage.π D.toOneStepDevissage.π
            (j ≫ pullback.fst h W.toBase ≫ V.toBase) ∧
          Nonempty (D'.toOneStepDevissage.G ≅
            (Scheme.Modules.pullback p).obj D.toOneStepDevissage.G) := by
  let : Smooth D.toOneStepDevissage.g := D.toOneStepDevissage.smooth
  let : Smooth V.toBase := by infer_instance
  let : Smooth U.toBase := by infer_instance
  let : Smooth h := smooth_of_etale_square V.toBase D.toOneStepDevissage.g U.toBase h hcomm
  obtain ⟨Wnew, hWnew, hWsmallAffine, O₁, o₁, hO₁aff, vPart, wPart, hvPartEt, hwPartSm,
      jRaw, hjOpen, hwgeom, hvwPart, hvPartPoint, hwPartPoint, hvPartIso, hjRaw_fst,
      hjRaw_snd⟩ :=
    exists_etaleShrinking_of_oneStepDevissageAt f F x D U hU V hV h hcomm hpoint
  let W_S : EtaleNeighborhood S (f x) :=
    { scheme := Wnew.scheme
      point := Wnew.point
      toBase := Wnew.toBase ≫ U.toBase
      map_point := (U.comp Wnew).map_point }
  have hW_S : W_S.IsElementary := hU.comp hWnew
  let : IsAffine W_S.scheme := hWsmallAffine
  let hs : W_S.toBase W_S.point = f x := W_S.map_point
  have hWraw : IsIso (W_S.toBase.residueFieldMap W_S.point) := W_S.isElementary_iff.1 hW_S
  let B : OneStepDevissage.BaseChangeData f F (f x) W_S.point W_S.toBase hs
      D.toOneStepDevissage :=
    OneStepDevissage.baseChange f F (f x) W_S.point
      W_S.toBase hs D.toOneStepDevissage
  let : LocallyOfFiniteType (pullback.snd f W_S.toBase) := B.locallyOfFiniteType
  let F₀ := (Scheme.Modules.pullback (pullback.fst f W_S.toBase)).obj F
  let : F₀.IsQuasicoherent := B.quasicoherent
  let : F₀.IsFiniteType := B.finiteType
  let yPB : (pullback D.toOneStepDevissage.g W_S.toBase : Scheme).carrier :=
    pullbackPointOfIsIsoResidueFieldMap D.toOneStepDevissage.g W_S.toBase
      D.y W_S.point (f x) D.g_y hs hW_S
  let yE : B.devissage.Y := B.y_square.isoPullback.inv yPB
  have hyE : B.pY yE = D.y :=
    isPullbackPointOfIsIsoResidueFieldMap_fst B.y_square D.y W_S.point (f x)
      D.g_y hs hW_S
  have hysE : B.devissage.g yE = W_S.point :=
    isPullbackPointOfIsIsoResidueFieldMap_snd B.y_square D.y W_S.point (f x)
      D.g_y hs hW_S
  have hpYiso : IsIso (B.pY.residueFieldMap yE) :=
    isIso_residueFieldMap_of_isPullback B.y_square yE
      (by rw [hysE]; exact hWraw)
  have hYiso : IsIso ((D.toOneStepDevissage.Y.residueFieldCongr hyE).inv ≫
      B.pY.residueFieldMap yE) :=
    IsIso.comp_isIso' ((D.toOneStepDevissage.Y.residueFieldCongr hyE).isIso_inv) hpYiso
  let zPB : (pullback D.toOneStepDevissage.π B.pY : Scheme).carrier :=
    pullbackPointOfIsIsoResidueFieldMap D.toOneStepDevissage.π B.pY
      D.z yE D.y D.π_z hyE hYiso
  let zE : B.devissage.Z := B.z_square.isoPullback.inv zPB
  have hzE : B.pZ zE = D.z :=
    isPullbackPointOfIsIsoResidueFieldMap_fst B.z_square D.z yE D.y
      D.π_z hyE hYiso
  have hπE : B.devissage.π zE = yE :=
    isPullbackPointOfIsIsoResidueFieldMap_snd B.z_square D.z yE D.y
      D.π_z hyE hYiso
  let xE : (pullback f W_S.toBase : Scheme).carrier :=
    pullbackPointOfIsIsoResidueFieldMap f W_S.toBase x W_S.point (f x) rfl hs hW_S
  have hxE : pullback.fst f W_S.toBase xE = x :=
    pullbackPointOfIsIsoResidueFieldMap_fst f W_S.toBase x W_S.point (f x) rfl hs hW_S
  have hxsE : pullback.snd f W_S.toBase xE = W_S.point :=
    pullbackPointOfIsIsoResidueFieldMap_snd f W_S.toBase x W_S.point (f x) rfl hs hW_S
  have hzsE : (B.devissage.π ≫ B.devissage.g) zE = W_S.point := by
    rw [Scheme.Hom.comp_apply, hπE]
    exact hysE
  let : IsIso ((S.residueFieldCongr hs).inv ≫ W_S.toBase.residueFieldMap W_S.point) := hW_S
  obtain ⟨E, hEdev, -, hEy⟩ := OneStepDevissageAt.exists_baseChange f F x D W_S.point
    W_S.toBase hs B xE hxE hxsE zE hzE hzsE yE hyE hysE
  have hucond : (vPart ≫ V.toBase) ≫ D.toOneStepDevissage.g =
      wPart ≫ W_S.toBase := by
    calc
      _ = vPart ≫ (V.toBase ≫ D.toOneStepDevissage.g) := by cat_disch
      _ = vPart ≫ (h ≫ U.toBase) := by rw [hcomm]
      _ = (vPart ≫ h) ≫ U.toBase := by cat_disch
      _ = (wPart ≫ Wnew.toBase) ≫ U.toBase := by rw [hvwPart]
      _ = wPart ≫ W_S.toBase := by rfl
  let uPB : O₁ ⟶
      pullback D.toOneStepDevissage.g W_S.toBase :=
    pullback.lift (vPart ≫ V.toBase) wPart hucond
  let u : O₁ ⟶ B.devissage.Y :=
    uPB ≫ B.y_square.isoPullback.inv
  have hu_pY : u ≫ B.pY = vPart ≫ V.toBase := by
    dsimp [u, uPB]
    rw [Category.assoc, B.y_square.isoPullback_inv_fst, pullback.lift_fst]
  have hu_g : u ≫ B.devissage.g = wPart := by
    dsimp [u, uPB]
    rw [Category.assoc, B.y_square.isoPullback_inv_snd, pullback.lift_snd]
  have huEt : Etale u := by
    have : Etale vPart := hvPartEt
    have : Etale B.pY := by
      rw [← B.y_square.isoPullback_hom_fst]
      infer_instance
    exact etale_of_comp_eq u B.pY hu_pY
  let Z₀ : Scheme.{u} := pullback B.devissage.π u
  let p₀ : Z₀ ⟶ B.devissage.Z := pullback.fst B.devissage.π u
  have hp₀Et : Etale p₀ := by
    dsimp [p₀, Z₀]
    infer_instance
  have : IsAffine B.devissage.Z := B.devissage.affine_Z
  have : IsAffine B.devissage.Y := B.devissage.affine_Y
  have : IsAffine O₁ := hO₁aff
  have : IsFinite B.devissage.π := B.devissage.finite
  have : IsAffineHom B.devissage.π := by infer_instance
  have hZ₀aff : IsAffine Z₀ := by
    dsimp [Z₀]
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      B.devissage.π u
  have hLiftExist := by
    have : IsAffine B.devissage.Z := B.devissage.affine_Z
    have : IsAffine (pullback f W_S.toBase : Scheme.{u}) := B.devissage.affine_X
    have : IsAffine Z₀ := hZ₀aff
    have : IsClosedImmersion B.devissage.i := B.devissage.closed_immersion
    have : Etale p₀ := hp₀Et
    exact Stacks.Etale.exists_etale_lift_of_isClosedImmersion B.devissage.i p₀
  obtain ⟨X₁, q, hX₁aff, hqEt, e, he⟩ := hLiftExist
  have hxy : D.toOneStepDevissage.g D.y = W_S.toBase W_S.point := by
    rw [D.g_y, W_S.map_point]
  have hfieldW : IsIso ((S.residueFieldCongr hxy.symm).inv ≫
      W_S.toBase.residueFieldMap W_S.point) := by
    infer_instance
  have huPBfst : pullback.fst D.toOneStepDevissage.g W_S.toBase
      (B.y_square.isoPullback.hom (u o₁)) = D.y := by
    have hmap : B.y_square.isoPullback.hom ≫ pullback.fst
        D.toOneStepDevissage.g W_S.toBase = B.pY :=
      B.y_square.isoPullback_hom_fst
    have hp := congrArg (fun k : B.devissage.Y ⟶ D.toOneStepDevissage.Y => k (u o₁)) hmap
    have hh := congrArg (fun k : O₁ ⟶ D.toOneStepDevissage.Y => k o₁) hu_pY
    calc
      _ = B.pY (u o₁) := hp
      _ = (vPart ≫ V.toBase) o₁ := hh
      _ = D.y := by simp [hvPartPoint, V.map_point]
  have huPBsnd : pullback.snd D.toOneStepDevissage.g W_S.toBase
      (B.y_square.isoPullback.hom (u o₁)) = W_S.point := by
    have hmap : B.y_square.isoPullback.hom ≫ pullback.snd
        D.toOneStepDevissage.g W_S.toBase = B.devissage.g :=
      B.y_square.isoPullback_hom_snd
    have hp := congrArg (fun k : B.devissage.Y ⟶ W_S.scheme => k (u o₁)) hmap
    have hh := congrArg (fun k : O₁ ⟶ W_S.scheme => k o₁) hu_g
    calc
      _ = B.devissage.g (u o₁) := hp
      _ = wPart o₁ := hh
      _ = W_S.point := hwPartPoint
  have hyPBfst : pullback.fst D.toOneStepDevissage.g W_S.toBase yPB = D.y :=
    pullbackPointOfIsIsoResidueFieldMap_fst D.toOneStepDevissage.g W_S.toBase
      D.y W_S.point (f x) D.g_y hs hW_S
  have hyPBsnd : pullback.snd D.toOneStepDevissage.g W_S.toBase yPB = W_S.point :=
    pullbackPointOfIsIsoResidueFieldMap_snd D.toOneStepDevissage.g W_S.toBase
      D.y W_S.point (f x) D.g_y hs hW_S
  have huPB : B.y_square.isoPullback.hom (u o₁) = yPB :=
    pullback_point_eq_of_isIso_residueFieldMap D.toOneStepDevissage.g W_S.toBase
      D.y W_S.point hxy hfieldW (B.y_square.isoPullback.hom (u o₁)) yPB
      huPBfst huPBsnd hyPBfst hyPBsnd
  have huPoint : u o₁ = yE := by
    show u o₁ = B.y_square.isoPullback.inv yPB
    rw [← huPB]
    simp
  have hVraw : IsIso (V.toBase.residueFieldMap V.point) := V.isElementary_iff.1 hV
  have hrightRaw : IsIso ((vPart ≫ V.toBase).residueFieldMap o₁) := by
    have hVpt : IsIso (V.toBase.residueFieldMap (vPart o₁)) := by
      rw [hvPartPoint]
      exact hVraw
    exact isIso_residueFieldMap_comp vPart V.toBase o₁ hvPartIso hVpt
  have huPointFst : (u ≫ B.pY) o₁ = D.y := by
    rw [hu_pY]
    simp [hvPartPoint, V.map_point]
  have hvPointFst : (vPart ≫ V.toBase) o₁ = D.y := by
    simp [hvPartPoint, V.map_point]
  have hleftNorm : IsIso ((D.toOneStepDevissage.Y.residueFieldCongr huPointFst).inv ≫
      (u ≫ B.pY).residueFieldMap o₁) := by
    rw [residueFieldCongr_inv_residueFieldMap_eq_of_eq hu_pY o₁ D.y huPointFst hvPointFst]
    infer_instance
  have hpyPoint : B.pY (u o₁) = D.y := by
    rw [← Scheme.Hom.comp_apply]
    exact huPointFst
  have hpYpt : IsIso (B.pY.residueFieldMap (u o₁)) := by
    rw [huPoint]
    exact hpYiso
  have hpYnorm : IsIso
      ((D.toOneStepDevissage.Y.residueFieldCongr hpyPoint).inv ≫
        B.pY.residueFieldMap (u o₁)) := by
    infer_instance
  have huNorm : IsIso
      ((B.devissage.Y.residueFieldCongr rfl).inv ≫ u.residueFieldMap o₁) :=
    isIso_residueFieldCongr_inv_residueFieldMap_of_comp u B.pY o₁ (u o₁) D.y rfl hpyPoint
      huPointFst hleftNorm hpYnorm
  have huRaw : IsIso (u.residueFieldMap o₁) :=
    IsIso.of_isIso_comp_left (B.devissage.Y.residueFieldCongr rfl).inv (u.residueFieldMap o₁)
  have huField : IsIso ((B.devissage.Y.residueFieldCongr huPoint).inv ≫
      u.residueFieldMap o₁) := by
    infer_instance
  let z₁ : Z₀ := pullbackPointOfIsIsoResidueFieldMap B.devissage.π u zE o₁ yE hπE huPoint huField
  have hz₁ : p₀ z₁ = zE :=
    pullbackPointOfIsIsoResidueFieldMap_fst B.devissage.π u zE o₁ yE hπE huPoint huField
  have hπ₁ : pullback.snd B.devissage.π u z₁ = o₁ :=
    pullbackPointOfIsIsoResidueFieldMap_snd B.devissage.π u zE o₁ yE hπE huPoint huField
  let i₁ : Z₀ ⟶ X₁ := e.hom ≫ pullback.snd B.devissage.i q
  let x₁ : X₁ := i₁ z₁
  have hBixFst : pullback.fst f W_S.toBase (B.devissage.i zE) = x := by
    have heq : B.pZ ≫ D.toOneStepDevissage.i =
        B.devissage.i ≫ pullback.fst f W_S.toBase := B.x_square.w
    have hh : (B.pZ ≫ D.toOneStepDevissage.i) zE =
        (B.devissage.i ≫ pullback.fst f W_S.toBase) zE :=
      congrArg (fun k : B.devissage.Z ⟶ X => k zE) heq
    have hproj : pullback.fst f W_S.toBase (B.devissage.i zE) =
        D.toOneStepDevissage.i (B.pZ zE) := by
      simpa only [Scheme.Hom.comp_apply] using hh.symm
    rwa [hzE, D.i_z] at hproj
  have hBixSnd : pullback.snd f W_S.toBase (B.devissage.i zE) = W_S.point := by
    calc
      pullback.snd f W_S.toBase (B.devissage.i zE) =
          (B.devissage.i ≫ pullback.snd f W_S.toBase) zE := rfl
      _ = (B.devissage.π ≫ B.devissage.g) zE := by
        have hh := congrArg (fun k : B.devissage.Z ⟶ W_S.scheme => k zE)
          B.devissage.over_base
        simpa only [Scheme.Hom.comp_apply] using hh
      _ = W_S.point := hzsE
  have hBix : B.devissage.i zE = xE :=
    (pullback_point_eq_of_isIso_residueFieldMap f W_S.toBase x W_S.point
      hs.symm hW_S xE (B.devissage.i zE) hxE hxsE hBixFst hBixSnd).symm
  have hLiftComm : p₀ ≫ B.devissage.i = i₁ ≫ q := by
    calc
      p₀ ≫ B.devissage.i = (e.hom ≫ pullback.fst B.devissage.i q) ≫ B.devissage.i := by
        rw [he]
      _ = e.hom ≫ (pullback.fst B.devissage.i q ≫ B.devissage.i) := by cat_disch
      _ = e.hom ≫ (pullback.snd B.devissage.i q ≫ q) := by
        rw [pullback.condition]
      _ = i₁ ≫ q := by dsimp [i₁]; cat_disch
  have hLiftSq : IsPullback p₀ i₁ B.devissage.i q :=
    IsPullback.of_iso_pullback ⟨hLiftComm⟩ e he rfl
  have hI₁closed : IsClosedImmersion i₁ := by
    let : IsClosedImmersion B.devissage.i := B.devissage.closed_immersion
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hLiftSq
      B.devissage.closed_immersion
  let p₁ : Z₀ ⟶ D.toOneStepDevissage.Z := p₀ ≫ B.pZ
  have hqX₁ : q x₁ = xE := by
    calc
      q x₁ = (i₁ ≫ q) z₁ := rfl
      _ = (p₀ ≫ B.devissage.i) z₁ := by rw [← hLiftSq.w]
      _ = B.devissage.i zE := by simp [hz₁]
      _ = xE := hBix
  let A : EtaleNeighborhood X x :=
    { scheme := X₁
      point := x₁
      toBase := q ≫ pullback.fst f W_S.toBase
      etale_toBase := by
        let : Etale (pullback.fst f W_S.toBase) := by infer_instance
        infer_instance
      map_point := by
        show pullback.fst f W_S.toBase (q x₁) = x
        rw [hqX₁, hxE] }
  let b : A.scheme ⟶ Wnew.scheme := q ≫ pullback.snd f W_S.toBase
  have hbPoint : b A.point = Wnew.point := by
    show pullback.snd f W_S.toBase (q x₁) = Wnew.point
    rw [hqX₁, hxsE]
  have hp₀raw : IsIso (p₀.residueFieldMap z₁) :=
    isIso_residueFieldMap_pullback_fst_of_right B.devissage.π u z₁ (by rw [hπ₁]; exact huRaw)
  have hBimap : IsIso (B.devissage.i.residueFieldMap zE) := by
    let : IsClosedImmersion B.devissage.i := B.devissage.closed_immersion
    exact isIso_residueFieldMap_of_isPreimmersion B.devissage.i zE
  have hi₁raw : IsIso (i₁.residueFieldMap z₁) := by
    let : IsClosedImmersion i₁ := hI₁closed
    exact isIso_residueFieldMap_of_isPreimmersion i₁ z₁
  have hcompPointR : (p₀ ≫ B.devissage.i) z₁ = xE := by
    show B.devissage.i (p₀ z₁) = xE
    rw [hz₁]
    exact hBix
  have hcompPointL : (i₁ ≫ q) z₁ = xE := hqX₁
  have hcompNormR := residueFieldCongr_inv_residueFieldMap_comp p₀ B.devissage.i
    z₁ zE xE hz₁ hBix hcompPointR
  have hcompNormRiso : IsIso
      (((pullback f W_S.toBase).residueFieldCongr hcompPointR).inv ≫
        (p₀ ≫ B.devissage.i).residueFieldMap z₁) := by
    rw [hcompNormR]
    infer_instance
  have hcompNormEq := residueFieldCongr_inv_residueFieldMap_eq_of_eq hLiftSq.w z₁ xE
    hcompPointR hcompPointL
  have hcompNormLiso : IsIso
      (((pullback f W_S.toBase).residueFieldCongr hcompPointL).inv ≫
        (i₁ ≫ q).residueFieldMap z₁) := by
    rw [← hcompNormEq]
    exact hcompNormRiso
  have hqNormComp := residueFieldCongr_inv_residueFieldMap_comp i₁ q z₁ x₁ xE rfl hqX₁
    hcompPointL
  have hi₁Norm : IsIso
      ((X₁.residueFieldCongr rfl).inv ≫ i₁.residueFieldMap z₁) := by
    infer_instance
  have hqNorm : IsIso
      (((pullback f W_S.toBase).residueFieldCongr hqX₁).inv ≫
        q.residueFieldMap x₁) := by
    rw [hqNormComp] at hcompNormLiso
    exact IsIso.of_isIso_comp_right _
      ((X₁.residueFieldCongr rfl).inv ≫ i₁.residueFieldMap z₁)
  have hpXraw : IsIso ((pullback.fst f W_S.toBase).residueFieldMap xE) :=
    isIso_residueFieldMap_pullback_fst_of_right f W_S.toBase xE (by
      rw [hxsE]
      exact hWraw)
  have hApt : (q ≫ pullback.fst f W_S.toBase) x₁ = x := A.map_point
  have hAcompNorm := residueFieldCongr_inv_residueFieldMap_comp q
    (pullback.fst f W_S.toBase) x₁ xE x hqX₁ hxE hApt
  have hAelementary : A.IsElementary := by
    show IsIso ((X.residueFieldCongr A.map_point).inv ≫
      A.toBase.residueFieldMap A.point)
    have hnorm : (X.residueFieldCongr A.map_point).inv ≫
        A.toBase.residueFieldMap A.point =
      ((X.residueFieldCongr hxE).inv ≫
        (pullback.fst f W_S.toBase).residueFieldMap xE) ≫
        (((pullback f W_S.toBase).residueFieldCongr hqX₁).inv ≫
          q.residueFieldMap x₁) := by
      have hbase : q ≫ pullback.fst f W_S.toBase = A.toBase := rfl
      have hnormComp :=
        residueFieldCongr_inv_residueFieldMap_eq_of_eq hbase.symm A.point x hApt A.map_point
      rw [← hnormComp, hAcompNorm]
      rfl
    rw [hnorm]
    infer_instance
  -- Every instance the rest of the proof needs is pinned here, in one block: each `haveI`
  -- invalidates the local instance cache, and the sheaf-of-modules instances over the new
  -- schemes are expensive to re-synthesize, so no instance is introduced after this point
  -- except by copying an already elaborated type (`haveI := h`).
  let : LocallyOfFiniteType (pullback.snd f W_S.toBase) := B.locallyOfFiniteType
  let : Etale q := hqEt
  have := B.devissage.quasi_coherent_G
  have := B.devissage.finite_type_G
  have : IsClosedImmersion B.devissage.i := B.devissage.closed_immersion
  have : IsAffineHom B.devissage.i := inferInstance
  have := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hLiftSq B.devissage.G
  let F' := (Scheme.Modules.pullback A.toBase).obj F
  let π₀ := pullback.snd B.devissage.π u
  let G₀ := (Scheme.Modules.pullback p₀).obj B.devissage.G
  let hl : LocallyOfFiniteType b := by dsimp [b]; infer_instance
  -- The types of these four are deliberately left to be inferred from the lemmas: writing
  -- `F'.IsQuasicoherent` out re-synthesizes the sheafification instances of the site of the
  -- new scheme, which is the single most expensive step in this proof.
  have hFqc := Stacks.Modules.isQuasicoherent_pullback A.toBase F ‹F.IsQuasicoherent›
  have hFft := Stacks.Modules.isFiniteType_pullback A.toBase F ‹F.IsFiniteType›
  have hGqc := Stacks.Modules.isQuasicoherent_pullback p₀ B.devissage.G
    B.devissage.quasi_coherent_G
  have hGft := Stacks.Modules.isFiniteType_pullback p₀ B.devissage.G
    B.devissage.finite_type_G
  have hZsq : IsPullback p₀ π₀ B.devissage.π u :=
    IsPullback.of_hasPullback B.devissage.π u
  have hmodule : F' ≅ (Scheme.Modules.pushforward i₁).obj G₀ :=
    ((Scheme.Modules.pullbackComp q (pullback.fst f W_S.toBase)).app F).symm ≪≫
      (Scheme.Modules.pullback q).mapIso B.devissage.module_iso ≪≫
      asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        hLiftSq.w).app B.devissage.G)
  have hGiso : Nonempty
      (G₀ ≅ (Scheme.Modules.pullback p₁).obj D.toOneStepDevissage.G) := by
    have hsource : G₀ =
        (Scheme.Modules.pullback p₀).obj
          ((Scheme.Modules.pullback B.pZ).obj D.toOneStepDevissage.G) := by
      dsimp [G₀]
      rw [B.module_eq]
    refine ⟨(eqToIso hsource) ≪≫ ?_⟩
    simpa [p₁] using (Scheme.Modules.pullbackComp p₀ B.pZ).app D.toOneStepDevissage.G
  have hfinite₀ : IsFinite π₀ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hZsq B.devissage.finite
  have hfinitePres₁ : AlgebraicGeometry.FinitePresentation i₁ :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hLiftSq
        B.devissage.finite_presentation.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hLiftSq
        B.devissage.finite_presentation.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hLiftSq
        B.devissage.finite_presentation.2.2⟩
  have hFN : SheafOfModules.supp F' = q ⁻¹' SheafOfModules.supp F₀ := by
    simp only [F', F₀, Stacks.Modules.supp_pullback,
      Set.preimage_preimage]
    rfl
  have hxSupport : (pullback.snd f W_S.toBase).asFiber (q x₁) ∈
      SheafOfModules.supp ((Scheme.Modules.pullback
        ((pullback.snd f W_S.toBase).fiberι ((pullback.snd f W_S.toBase) (q x₁)))).obj F₀) := by
    rw [hqX₁]
    exact E.mem_fiber_support
  have hxDimension : topologicalKrullDimAt
      (SheafOfModules.supp ((Scheme.Modules.pullback
        ((pullback.snd f W_S.toBase).fiberι ((pullback.snd f W_S.toBase) (q x₁)))).obj F₀))
      ⟨(pullback.snd f W_S.toBase).asFiber (q x₁), hxSupport⟩ =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback
          ((pullback.snd f W_S.toBase).fiberι ((pullback.snd f W_S.toBase) (q x₁)))).obj F₀)) := by
    revert hxSupport
    rw [hqX₁]
    intro hxSupport
    exact E.dimension
  obtain ⟨hxNew, hdimNew, hdimAtNew⟩ := exists_mem_supp_fiber_dimension_of_etale
    q (pullback.snd f W_S.toBase) F₀ F' hFN x₁ hxSupport hxDimension
  have hdimSupport : topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (b.fiberι (b A.point))).obj F')) =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback
          ((pullback.snd f W_S.toBase).fiberι W_S.point)).obj F₀)) :=
    hdimNew.trans (congrArg (fun t : W_S.scheme =>
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback
          ((pullback.snd f W_S.toBase).fiberι t)).obj F₀)))
      ((congrArg (pullback.snd f W_S.toBase) hqX₁).trans hxsE))
  have hPTold := purelyTranscendental_of_heq (pullback.snd f W_S.toBase) F₀ xE E
    W_S.point hxsE B.devissage yE hEdev hEy hysE
  have := hl
  have := hFqc
  have := hFft
  let D' : OneStepDevissageAt b F' A.point := {
    toOneStepDevissage := {
      Z := Z₀
      Y := O₁
      i := i₁
      π := π₀
      g := wPart
      G := G₀
      quasi_coherent_G := hGqc
      finite_type_G := hGft
      over_base := by
        show i₁ ≫ b = π₀ ≫ wPart
        calc
          i₁ ≫ b = (i₁ ≫ q) ≫ pullback.snd f W_S.toBase := by cat_disch
          _ = (p₀ ≫ B.devissage.i) ≫ pullback.snd f W_S.toBase := by
            rw [hLiftSq.w]
          _ = p₀ ≫ (B.devissage.i ≫ pullback.snd f W_S.toBase) := by cat_disch
          _ = p₀ ≫ (B.devissage.π ≫ B.devissage.g) := by
            rw [B.devissage.over_base]
          _ = (p₀ ≫ B.devissage.π) ≫ B.devissage.g := by cat_disch
          _ = (π₀ ≫ u) ≫ B.devissage.g := by rw [pullback.condition]
          _ = π₀ ≫ (u ≫ B.devissage.g) := by cat_disch
          _ = π₀ ≫ wPart := by rw [hu_g]
      affine_X := hX₁aff
      affine_S := hWsmallAffine
      affine_Z := hZ₀aff
      affine_Y := hO₁aff
      closed_immersion := hI₁closed
      finite_presentation := hfinitePres₁
      module_iso := hmodule
      finite := hfinite₀
      smooth := hwPartSm
      geometrically_irreducible := hwgeom
      fiber_dimension := by
        intro t
        rw [hdimSupport]
        let : Etale u := huEt
        let : Smooth B.devissage.g := B.devissage.smooth
        let : GeometricallyIrreducible B.devissage.g := B.devissage.geometrically_irreducible
        have : GeometricallyIrreducible (u ≫ B.devissage.g) := by
          rw [hu_g]
          exact hwgeom
        calc
          topologicalKrullDim (wPart.fiber t) =
              topologicalKrullDim ((u ≫ B.devissage.g).fiber t) := by rw [hu_g]
          _ = topologicalKrullDim (B.devissage.g.fiber t) :=
            topologicalKrullDim_fiber_comp_eq_of_etale u B.devissage.g t
          _ = _ := B.devissage.fiber_dimension t
    }
    mem_fiber_support := hxNew
    dimension := hdimAtNew
    z := z₁
    y := o₁
    i_z := rfl
    π_z := hπ₁
    g_y := by
      show wPart o₁ = b x₁
      rw [hwPartPoint, hbPoint]
    fiber_eq_singleton := by
      refine preimage_singleton_of_isPullback (hZsq.paste_horiz B.z_square) D.z D.y
        D.fiber_eq_singleton z₁ o₁ ?_ ?_ hπ₁ ?_
      · rw [Scheme.Hom.comp_apply, hz₁]
        exact hzE
      · rw [Scheme.Hom.comp_apply, huPoint]
        exact hyE
      · rw [Scheme.residueFieldMap_comp]
        exact IsIso.comp_isIso' hpYpt huRaw
    residueField_purelyTranscendental :=
      purelyTranscendental_comp_congr B.devissage.g u wPart hu_g o₁ yE W_S.point
        (b A.point) huPoint hysE hwPartPoint hbPoint.symm huField hPTold }
  let j : D'.toOneStepDevissage.Y ⟶ pullback h Wnew.toBase := jRaw
  let p : D'.toOneStepDevissage.Z ⟶ D.toOneStepDevissage.Z := p₁
  have hPBX : IsPullback p₁ i₁ D.toOneStepDevissage.i A.toBase := by
    dsimp [p₁, A]
    simpa only [Category.assoc] using hLiftSq.paste_horiz B.x_square
  have hbaseπ : jRaw ≫ pullback.fst h Wnew.toBase ≫ V.toBase = u ≫ B.pY := by
    rw [← Category.assoc, hjRaw_fst, hu_pY]
  have hPBπ : IsPullback p₁ π₀ D.toOneStepDevissage.π
      (jRaw ≫ pullback.fst h Wnew.toBase ≫ V.toBase) := by
    rw [hbaseπ]
    show IsPullback (p₀ ≫ B.pZ) π₀ D.toOneStepDevissage.π (u ≫ B.pY)
    exact hZsq.paste_horiz B.z_square
  have hbaseeq : A.toBase ≫ f = b ≫ Wnew.toBase ≫ U.toBase := by
    dsimp [A, b, W_S]
    calc
      (q ≫ pullback.fst f W_S.toBase) ≫ f =
          q ≫ (pullback.fst f W_S.toBase ≫ f) := by cat_disch
      _ = q ≫ (pullback.snd f W_S.toBase ≫ W_S.toBase) := by
        rw [pullback.condition]
      _ = q ≫ pullback.snd f W_S.toBase ≫ Wnew.toBase ≫ U.toBase := by rfl
      _ = (q ≫ pullback.snd f W_S.toBase) ≫ Wnew.toBase ≫ U.toBase := by cat_disch
  have hyFst : (jRaw ≫ pullback.fst h Wnew.toBase) o₁ = V.point := by
    rwa [hjRaw_fst]
  have hzFst : p₁ z₁ = D.z := by
    show (p₀ ≫ B.pZ) z₁ = D.z
    rw [Scheme.Hom.comp_apply, hz₁]
    exact hzE
  exact ⟨Wnew, hWnew, A, hAelementary, b, hbPoint, hbaseeq, hl, hFqc, hFft, D', j, p,
    hjOpen, hjRaw_snd.symm, hyFst, hzFst, hPBX.w.symm, hPBX, hPBπ, hGiso⟩

end AlgebraicGeometry

end
