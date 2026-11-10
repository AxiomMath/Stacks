module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparisonTrivial
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus0BDP
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankDecomposition

/-!
# Tag 0BF1: the descent locus does not shrink near a point with injective `H¹`

Consider `f : X ⟶ S` and `f' : X' ⟶ S` satisfying the hypotheses of [Stacks, Tag 0BDP] (flat,
proper, of finite presentation, with `𝒪_T ≅ p_* 𝒪_{X_T}` after every base change), a morphism
`i : X' ⟶ X` over `S`, an invertible `𝒪_X`-module `L` and `L' = i^* L`. [Stacks, Tag 0BF1] says:
if `s` lies in the locally closed subscheme `Z ⊆ S` of Tag 0BDP for `(f, L)` and
`H¹(X_s, 𝒪) → H¹(X'_s, 𝒪)` is injective, then `Z ∩ U = Z' ∩ U` for an open neighbourhood `U`
of `s`, where `Z'` is the subscheme for `(f', L')`.

## How the statement is rendered

Tag 0BDP constructs `Z` as the scheme representing the descent condition
`AlgebraicGeometry.DescendsFromBase f L`: a morphism `g : T ⟶ S` factors through `Z` exactly when
`L` pulled back to `X ×_S T` is the pullback of a finite locally free module on `T`. The
representability itself (`AlgebraicGeometry.HasDescentLocus`) is not available, so the statement
here is written through the functor `Z` represents, which determines it:

* `s ∈ Z` is "`Spec κ(s) ⟶ S` factors through `Z`", i.e.
  `DescendsFromBase f L (S.fromSpecResidueField s)`;
* `Z ∩ U = Z' ∩ U` is "a morphism `g : T ⟶ S` with image in `U` factors through `Z` exactly
  when it factors through `Z'`", i.e. `DescendsFromBase f L g ↔ DescendsFromBase f' L' g`.

Whenever representing objects `Z`, `Z'` exist the two readings agree; the statement for them is
`AlgebraicGeometry.IsDescentLocus.exists_open_factorsThrough_iff`.

## Main results

* `AlgebraicGeometry.descendsFromBase_modulePullback_of_comp`: the containment `Z ⊆ Z'`.
* `AlgebraicGeometry.exists_open_descendsFromBase_iff`: **Tag 0BF1**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **The descent condition is inherited by a pullback along a morphism over the base.** Let
`i : X' ⟶ X` satisfy `i ≫ f = f'`. If `L` on `X` descends from the base along `g : T ⟶ S`, then
so does its pullback `i^* L` on `X'`: the module `N` on `T` witnessing the first condition
witnesses the second as well. This is the containment `Z ⊆ Z'` of [Stacks, Tag 0BF1]. -/
theorem descendsFromBase_modulePullback_of_comp {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
    (i : X' ⟶ X) (hi : i ≫ f = f')
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {T : Scheme.{u}} (g : T ⟶ S) (hd : DescendsFromBase f L g) :
    DescendsFromBase f' ((modulePullback i.toLRSHom.toShHom).obj L) g := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hd
  refine ⟨N, hN, ?_⟩
  obtain ⟨j, hjfst, hjsnd⟩ : ∃ j : pullback f' g ⟶ pullback f g,
      j ≫ pullback.fst f g = pullback.fst f' g ≫ i ∧
        j ≫ pullback.snd f g = pullback.snd f' g :=
    ⟨pullback.lift (pullback.fst f' g ≫ i) (pullback.snd f' g)
        (by rw [Category.assoc, hi]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have comp : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C), a ≫ b = c →
      ∀ M, Nonempty ((modulePullback c.toLRSHom.toShHom).obj M ≅
        (modulePullback a.toLRSHom.toShHom).obj ((modulePullback b.toLRSHom.toShHom).obj M)) := by
    rintro A B C a b c rfl M
    exact ⟨(modulePullbackComp a.toLRSHom.toShHom b.toLRSHom.toShHom).app M⟩
  obtain ⟨esnd⟩ := comp j _ _ hjsnd N
  obtain ⟨efst⟩ := comp j _ _ hjfst L
  obtain ⟨efst'⟩ := comp (pullback.fst f' g) i _ rfl L
  exact ⟨esnd ≪≫ (modulePullback j.toLRSHom.toShHom).mapIso e ≪≫ efst.symm ≪≫ efst'⟩

namespace DescentLocusComparison

/-- **`𝒪_T ≅ p_* 𝒪_{X_T}` over an affine base gives `Γ(X_T, 𝒪) = B`.** -/
theorem bijective_baseRingHom_of_isIso {B : Type u} [CommRing B] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of B)) (hO : IsIso (structureSheafHom h.toLRSHom.toShHom)) :
    Function.Bijective (Stacks.Cech.baseRingHom h ⊤).hom := by
  have h1 : IsIso ((structureSheafHom h.toLRSHom.toShHom).hom.app (op ⊤)) := by
    have : IsIso (structureSheafHom h.toLRSHom.toShHom).hom :=
      (ObjectProperty.ι _).map_isIso (structureSheafHom h.toLRSHom.toShHom)
    infer_instance
  have h2 : Function.Bijective (h.appTop).hom :=
    ConcreteCategory.bijective_of_isIso ((structureSheafHom h.toLRSHom.toShHom).hom.app (op ⊤))
  have h4 : (Stacks.Cech.baseRingHom h ⊤).hom = (Stacks.Cech.globalRingHom h).hom := by
    change (Stacks.Cech.globalRingHom h ≫ Y.presheaf.map (homOfLE le_top).op).hom = _
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [h4]
  have h5 : Function.Bijective (toSpecΓ (CommRingCat.of B)).hom :=
    ConcreteCategory.bijective_of_isIso _
  exact h2.comp h5

/-- **A finite locally free module of two ranks on a nonempty scheme has equal ranks.** -/
theorem eq_of_isFiniteLocallyFreeOfRank {Y : Scheme.{u}} (M : Y.Modules) (y : Y) {r s : ℕ}
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r)
    (hs : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s) : r = s := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.toRingSheafModule M) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  obtain ⟨q, hq, hqr⟩ := hr.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨q', hq', hqs⟩ := hs.exists_isFiniteLocallyFreeOfRankData
  have hcov : ∀ (p : _root_.SheafOfModules.LocalGeneratorsData.{u} M), ∃ i, y ∈ p.X i := by
    intro p
    have h : (⨆ i, p.X i) = ⊤ := (Opens.coversTop_iff _ p.X).1 p.coversTop
    have hy : y ∈ (⨆ i, p.X i) := h ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, hi⟩ := hcov q
  obtain ⟨j, hj⟩ := hcov q'
  have h1 := Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card
    (Scheme.Modules.toRingSheafModule M) (LocallyFreeRank.scheme_stalksNontrivial Y) q hq i y hi
  have h2 := Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card
    (Scheme.Modules.toRingSheafModule M) (LocallyFreeRank.scheme_stalksNontrivial Y) q' hq' j y hj
  rw [Nat.card_congr (hqr i).some, Nat.card_fin] at h1
  rw [Nat.card_congr (hqs j).some, Nat.card_fin] at h2
  rw [← h1, ← h2]

/-- **An invertible module isomorphic to a finite free module on a nonempty scheme is trivial.**
-/
theorem nonempty_iso_unit_of_iso_free {Y : Scheme.{u}} (y : Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] {I : Type u} [Finite I]
    (e : M ≅ _root_.SheafOfModules.free (R := Y.ringCatSheaf) I) :
    Nonempty (M ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  have hI : Nat.card I = 1 := by
    have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1 := inferInstance
    have h2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M (Nat.card I) :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm
        (SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv I (Nat.card I)
          (Finite.equivFin I))
    exact eq_of_isFiniteLocallyFreeOfRank M y h2 h1
  obtain ⟨h1, ⟨i₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hI
  have : Unique I := ⟨⟨i₀⟩, fun j => h1.elim j i₀⟩
  exact ⟨e ≪≫ Stacks.SheafOfModules.Invertible.freeUniqueIso I⟩

/-- **Base change along a composite, as a cartesian square over the first factor.** For
`f : X ⟶ S`, `ι : S₁ ⟶ S` and `z : Z ⟶ S₁`, the base change of `f` along `w = z ≫ ι` is the base
change of `X ×_S S₁ ⟶ S₁` along `z`. -/
theorem isPullback_lift_comp {S S₁ X Z : Scheme.{u}} (f : X ⟶ S) (ι : S₁ ⟶ S) (z : Z ⟶ S₁)
    (w : Z ⟶ S) (hw : z ≫ ι = w) :
    IsPullback (pullback.lift (pullback.fst f w) (pullback.snd f w ≫ z)
        (by rw [Category.assoc, hw]; exact pullback.condition) : pullback f w ⟶ pullback f ι)
      (pullback.snd f w) (pullback.snd f ι) z := by
  subst hw
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f ι)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback f (z ≫ ι)

/-- A global function whose basic open is everything is a unit. -/
theorem isUnit_of_basicOpen_eq_top {Y : Scheme.{u}} (r : Γ(Y, ⊤)) (h : Y.basicOpen r = ⊤) :
    IsUnit r :=
  Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ r fun x _ =>
    (Y.mem_basicOpen_top r x).1 (by rw [h]; trivial)

/-- A global function which vanishes on a neighbourhood of every point is zero. -/
theorem eq_zero_of_forall_exists_res_eq_zero {Y : Scheme.{u}} (r : Γ(Y, ⊤))
    (h : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ Y.presheaf.map (homOfLE le_top : V ⟶ ⊤).op r = 0) :
    r = 0 := by
  refine TopCat.Presheaf.section_ext Y.sheaf ⊤ r 0 fun y hy => ?_
  obtain ⟨V, hyV, hV⟩ := h y
  have h1 := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE le_top) y hyV r
  rw [hV, map_zero] at h1
  rw [map_zero]
  exact h1.symm

/-- Pulling back along `q` is pulling back along `p` and then along `j`, when `j ≫ p = q`. -/
private noncomputable def pullbackIsoOfComp {Y Y' Z : Scheme.{u}} (j : Y ⟶ Y') (p : Y' ⟶ Z)
    (q : Y ⟶ Z) (h : j ≫ p = q) (M : Z.Modules) :
    (Scheme.Modules.pullback q).obj M ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj M) :=
  ((Scheme.Modules.pullbackCongr h).app M).symm ≪≫ ((Scheme.Modules.pullbackComp j p).app M).symm

/-- **A local free presentation of `N` pulls back to any scheme mapping into its domain.** -/
theorem nonempty_iso_free_of_factor {T Y : Scheme.{u}} (N : T.Modules) (V : T.Opens)
    {I : Type u} (e : N.restrict V.ι ≅ _root_.SheafOfModules.free (R := V.toScheme.ringCatSheaf) I)
    (g : Y ⟶ T) (j : Y ⟶ V.toScheme) (hj : j ≫ V.ι = g) :
    Nonempty ((Scheme.Modules.pullback g).obj N ≅
      _root_.SheafOfModules.free (R := Y.ringCatSheaf) I) :=
  ⟨pullbackIsoOfComp j V.ι g hj N ≪≫
    (Scheme.Modules.pullback j).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫ e) ≪≫
    Scheme.Modules.pullbackFreeIso j I⟩

/-- **Descent along `g` makes the module locally free near every point of `T`.** If `E`
descends from the base along `g : T ⟶ S`, every point of `T` has an open neighbourhood `U` and a
finite type `I` such that for every `v : Y ⟶ T` with image in `U` the pullback of `E` to
`X ×_S Y` is free on `I`. -/
theorem exists_free_of_descendsFromBase {X S T : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
    (g : T ⟶ S) (hd : DescendsFromBase f E g) (t : T) :
    ∃ U : T.Opens, t ∈ U ∧ ∃ (I : Type u) (_ : Finite I),
      ∀ {Y : Scheme.{u}} (v : Y ⟶ T) (g' : Y ⟶ S), v ≫ g = g' → Set.range v.base ⊆ U →
        Nonempty ((Scheme.Modules.pullback (pullback.fst f g')).obj E ≅
          _root_.SheafOfModules.free (R := (pullback f g').ringCatSheaf) I) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hd
  obtain ⟨U, htU, I, hI, ⟨eU⟩⟩ := (Scheme.Modules.isFiniteLocallyFree_iff N).2 hN t
  refine ⟨U, htU, I, hI, fun {Y} v g' hv hvU => ?_⟩
  have hrange : Set.range v.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hvU
  obtain ⟨eN⟩ := nonempty_iso_free_of_factor N U eU v (IsOpenImmersion.lift U.ι v hrange)
    (IsOpenImmersion.lift_fac _ _ _)
  set j : pullback f g' ⟶ pullback f g := pullback.lift (pullback.fst f g')
    (pullback.snd f g' ≫ v) (by rw [Category.assoc, hv]; exact pullback.condition)
  have hj1 : j ≫ pullback.fst f g = pullback.fst f g' := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd f g = pullback.snd f g' ≫ v := pullback.lift_snd _ _ _
  have e' : (Scheme.Modules.pullback (pullback.snd f g)).obj N ≅
      (Scheme.Modules.pullback (pullback.fst f g)).obj E := e
  exact ⟨pullbackIsoOfComp j _ _ hj1 E ≪≫
    (Scheme.Modules.pullback j).mapIso e'.symm ≪≫
    (pullbackIsoOfComp j _ _ hj2 N).symm ≪≫
    pullbackIsoOfComp (pullback.snd f g') v _ rfl N ≪≫
    (Scheme.Modules.pullback (pullback.snd f g')).mapIso eN ≪≫
    Scheme.Modules.pullbackFreeIso _ I⟩

/-- An invertible module on a scheme flat over a base is flat over that base. -/
theorem isFlatOver_of_isInvertible {Y Z : Scheme.{u}} (h : Y ⟶ Z) [Flat h] (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] :
    IsFlatOver h.toLRSHom.toShHom M := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1
  exact VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree h M

end DescentLocusComparison

open DescentLocusComparison in
/-- **Stacks Tag 0BF1.** Let `f : X ⟶ S` and `f' : X' ⟶ S` satisfy the hypotheses of
[Stacks, Tag 0BDP] — flat, proper, of finite presentation, with `𝒪_T ⟶ p_* 𝒪_{X_T}` an
isomorphism after every base change `T ⟶ S` — and let `i : X' ⟶ X` be a morphism over `S`, `L` an
invertible `𝒪_X`-module and `L' = i^* L`. Let `s ∈ S` be a point of the descent locus `Z` of
`(f, L)` at which `H¹(X_s, 𝒪) → H¹(X'_s, 𝒪)` is injective. Then `Z ∩ U = Z' ∩ U` for an open
neighbourhood `U` of `s`, where `Z'` is the descent locus of `(f', L')`.

**Rendering.** The locus `Z` of Tag 0BDP is the subscheme representing the descent condition
`AlgebraicGeometry.DescendsFromBase f L` (a morphism `g : T ⟶ S` factors through `Z` exactly when
`L` pulled back to `X ×_S T` comes from a finite locally free module on `T`), and likewise `Z'`
for `(f', L')`. The statement is written through the functors these subschemes represent, which
determine them: `s ∈ Z` is `DescendsFromBase f L (S.fromSpecResidueField s)`, and
`Z ∩ U = Z' ∩ U` is the equivalence of the two descent conditions for every `g : T ⟶ S` with
image in `U`. The fibre map `X'_s ⟶ X_s` is `pullback.map` of `i`, and the map on `H¹` is the
pullback map of [Stacks, Tag 01FA] on the structure sheaf, read in `H¹(X'_s, 𝒪_{X'_s})` through
the canonical `(X'_s ⟶ X_s)^* 𝒪_{X_s} ≅ 𝒪_{X'_s}`. The containment `Z ⊆ Z'` is
`descendsFromBase_modulePullback_of_comp`; the same statement for given representing objects
`Z`, `Z'` is `AlgebraicGeometry.IsDescentLocus.exists_open_factorsThrough_iff`. -/
@[stacks 0BF1]
theorem exists_open_descendsFromBase_iff {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
    (i : X' ⟶ X) (hi : i ≫ f = f')
    [Flat f] [IsProper f] (hfp : FinitePresentation f)
    (hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    [Flat f'] [IsProper f'] (hfp' : FinitePresentation f')
    (hfO' : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f' a).toLRSHom.toShHom))
    (L : X.Modules) [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (s : S) (hs : DescendsFromBase f L (S.fromSpecResidueField s))
    (hH1 : Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap
      (pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hi])
        (by rw [Category.comp_id, Category.id_comp])).toLRSHom.toShHom
      1 (SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) ≫
        (Stacks.Cohomology.moduleCohomologyAlong
          (pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id, hi])
            (by rw [Category.comp_id, Category.id_comp])).toLRSHom.toShHom 1).map
          (Scheme.Modules.pullbackUnitIso
            (pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _)
              (𝟙 _) (by rw [Category.comp_id, hi])
              (by rw [Category.comp_id, Category.id_comp]))).hom)) :
    ∃ U : S.Opens, s ∈ U ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S), Set.range g.base ⊆ U →
      (DescendsFromBase f L g ↔ DescendsFromBase f' ((Scheme.Modules.pullback i).obj L) g) := by
  classical
  have := hfp.locallyOfFinitePresentation
  have := hfp'.locallyOfFinitePresentation
  -- an affine open neighbourhood `V = Spec A` of `s`
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  let A : Type u := Γ(S, V)
  let ι : Spec (.of A) ⟶ S := hV.fromSpec
  have hιr : Set.range ι = V := hV.range_fromSpec
  have : IsOpenImmersion ι := IsAffineOpen.isOpenImmersion_fromSpec hV
  -- the base changes to `Spec A`
  let fA : pullback f ι ⟶ Spec (.of A) := pullback.snd f ι
  let f'A : pullback f' ι ⟶ Spec (.of A) := pullback.snd f' ι
  let qA := pullback.fst f ι
  let q'A := pullback.fst f' ι
  let aA : pullback f' ι ⟶ pullback f ι :=
    pullback.lift (q'A ≫ i) f'A (by rw [Category.assoc, hi]; exact pullback.condition)
  have haA : aA ≫ fA = f'A := pullback.lift_snd _ _ _
  have haA' : aA ≫ qA = q'A ≫ i := pullback.lift_fst _ _ _
  have : LocallyOfFinitePresentation fA :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f ι))
  have : LocallyOfFinitePresentation f'A :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f' ι))
  have : IsProper fA := inferInstanceAs (IsProper (pullback.snd f ι))
  have : IsProper f'A := inferInstanceAs (IsProper (pullback.snd f' ι))
  have : Flat fA := inferInstanceAs (Flat (pullback.snd f ι))
  have : Flat f'A := inferInstanceAs (Flat (pullback.snd f' ι))
  set LA := (Scheme.Modules.pullback qA).obj L with hLA_def
  have hLA : IsFlatOver fA.toLRSHom.toShHom LA := isFlatOver_of_isInvertible fA LA
  have hL'A : IsFlatOver f'A.toLRSHom.toShHom ((Scheme.Modules.pullback aA).obj LA) :=
    isFlatOver_of_isInvertible f'A _
  -- the fibres over `s`
  have hsr : Set.range (S.fromSpecResidueField s) ⊆ Set.range ι := by
    rw [Scheme.range_fromSpecResidueField, hιr]
    simpa using hsV
  let m := IsOpenImmersion.lift ι (S.fromSpecResidueField s) hsr
  have hm : m ≫ ι = S.fromSpecResidueField s := IsOpenImmersion.lift_fac _ _ _
  let χ₀ : A →+* S.residueField s := (Spec.preimage m).hom
  have hχ₀ : Spec.map (CommRingCat.ofHom χ₀) = m := by
    simp only [χ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hχ₀ι : Spec.map (CommRingCat.ofHom χ₀) ≫ ι = S.fromSpecResidueField s := by
    rw [hχ₀, hm]
  have hsq₀ := isPullback_lift_comp f ι _ _ hχ₀ι
  have hsq'₀ := isPullback_lift_comp f' ι _ _ hχ₀ι
  set a₀ := pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hi]) (by rw [Category.comp_id, Category.id_comp])
  have ha₀ : a₀ ≫ pullback.snd f (S.fromSpecResidueField s) =
      pullback.snd f' (S.fromSpecResidueField s) := by
    simp only [a₀, pullback.map, pullback.lift_snd, Category.comp_id]
  have hH1' : Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap
      a₀.toLRSHom.toShHom 1
        (SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)) :=
    fun x y hxy => hH1 (congrArg (ConcreteCategory.hom ((Stacks.Cohomology.moduleCohomologyAlong
      a₀.toLRSHom.toShHom 1).map (Scheme.Modules.pullbackUnitIso a₀).hom)) hxy)
  set q₀A : pullback f (S.fromSpecResidueField s) ⟶ pullback f ι := pullback.lift
    (pullback.fst f (S.fromSpecResidueField s))
    (pullback.snd f (S.fromSpecResidueField s) ≫ Spec.map (CommRingCat.ofHom χ₀))
    (by rw [Category.assoc]; exact pullback.condition.trans (congrArg (_ ≫ ·) hχ₀ι.symm))
  set q'₀A : pullback f' (S.fromSpecResidueField s) ⟶ pullback f' ι := pullback.lift
    (pullback.fst f' (S.fromSpecResidueField s))
    (pullback.snd f' (S.fromSpecResidueField s) ≫ Spec.map (CommRingCat.ofHom χ₀))
    (by rw [Category.assoc]; exact pullback.condition.trans (congrArg (_ ≫ ·) hχ₀ι.symm))
  have hcomm : a₀ ≫ q₀A = q'₀A ≫ aA := by
    apply pullback.hom_ext
    · simp only [Category.assoc, q₀A, q'₀A, aA, q'A, a₀, pullback.lift_fst, pullback.map,
        pullback.lift_fst_assoc]
    · simp only [Category.assoc, q₀A, q'₀A, aA, f'A, a₀, pullback.lift_snd, pullback.map,
        pullback.lift_snd_assoc, Category.comp_id]
  have hΓ₀ := bijective_baseRingHom_of_isIso (pullback.snd f (S.fromSpecResidueField s))
    (hfO (S.fromSpecResidueField s))
  have hΓ'₀ := bijective_baseRingHom_of_isIso (pullback.snd f' (S.fromSpecResidueField s))
    (hfO' (S.fromSpecResidueField s))
  -- the fibre `X_s` is nonempty
  have hne : Nonempty ((pullback f (S.fromSpecResidueField s) : Scheme.{u}) : Type u) := by
    by_contra hcon
    have : IsEmpty ((pullback f (S.fromSpecResidueField s) : Scheme.{u}) : Type u) :=
      not_nonempty_iff.1 hcon
    exact zero_ne_one (hΓ₀.1 (Subsingleton.elim
      ((Stacks.Cech.baseRingHom (pullback.snd f (S.fromSpecResidueField s)) ⊤).hom 0)
      ((Stacks.Cech.baseRingHom (pullback.snd f (S.fromSpecResidueField s)) ⊤).hom 1)))
  obtain ⟨x₀⟩ := hne
  -- `s ∈ Z`: `L` is trivial on `X_s`
  have hL₀ : Nonempty ((Scheme.Modules.pullback q₀A).obj LA ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) := by
    obtain ⟨ξ⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
    obtain ⟨U₀, hξ, I₀, _, hfree⟩ := exists_free_of_descendsFromBase f L _ hs ξ
    let v : Spec (S.residueField s) ⟶ Spec (S.residueField s) := 𝟙 _
    have hU₀ : Set.range v.base ⊆ U₀ := by
      rintro y -
      rwa [Subsingleton.elim y ξ]
    obtain ⟨e⟩ := hfree v _ (Category.id_comp _) hU₀
    have hq : q₀A ≫ qA = pullback.fst f (S.fromSpecResidueField s) := pullback.lift_fst _ _ _
    exact nonempty_iso_unit_of_iso_free x₀ ((Scheme.Modules.pullback q₀A).obj LA)
      ((pullbackIsoOfComp q₀A qA _ hq L).symm ≪≫ e)
  obtain ⟨G, hG, n, c, hc, hI, hIII⟩ := exists_vanishing_family_trivial aA fA f'A haA LA hLA hL'A
    χ₀ hsq₀ hsq'₀ a₀ ha₀ hcomm hL₀ hΓ₀ hΓ'₀ hH1'
  -- the neighbourhood: the image of `D(G) ⊆ Spec A`
  let D : (Spec (.of A)).Opens := (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv G)
  have hD : (D : Set (Spec (.of A))) = (PrimeSpectrum.basicOpen G : Set (PrimeSpectrum A)) :=
    congrArg SetLike.coe (basicOpen_eq_of_affine (R := CommRingCat.of A) G)
  let U : S.Opens := ⟨ι.base '' (D : Set (Spec (.of A))), ι.isOpenEmbedding.isOpenMap _ D.isOpen⟩
  refine ⟨U, ?_, fun {T} g hg => ⟨descendsFromBase_modulePullback_of_comp f f' i hi L g,
    fun hd' => ?_⟩⟩
  · obtain ⟨ξ⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
    refine ⟨m.base ξ, ?_, ?_⟩
    · rw [hD, ← hχ₀]
      change G ∉ Ideal.comap χ₀ (ξ : PrimeSpectrum (S.residueField s)).asIdeal
      rw [Ideal.mem_comap]
      exact fun h => ξ.isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h (isUnit_iff_ne_zero.2 hG))
    · rw [← Scheme.Hom.comp_apply, hm]
      exact (Set.ext_iff.1 (Scheme.range_fromSpecResidueField (X := S) s) _).1 ⟨ξ, rfl⟩
  -- a morphism `g : T ⟶ S` with image in `U`
  have hgr : Set.range g.base ⊆ Set.range ι.base := hg.trans (Set.image_subset_range _ _)
  let gT := IsOpenImmersion.lift ι g hgr
  have hgT : gT ≫ ι = g := IsOpenImmersion.lift_fac _ _ _
  have hgD : ∀ t, gT.base t ∈ D := fun t => by
    obtain ⟨y, hy, hyt⟩ := hg ⟨t, rfl⟩
    have h1 : ι.base y = ι.base (gT.base t) := by rw [hyt, ← Scheme.Hom.comp_apply, hgT]
    rw [← ι.isOpenEmbedding.injective h1]
    exact hy
  let φT : A →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ gT.appTop).hom
  have hφT : T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φT) = gT := by
    rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hφTG : IsUnit (φT G) := by
    refine isUnit_of_basicOpen_eq_top _ ?_
    change T.basicOpen (gT.appTop ((Scheme.ΓSpecIso (.of A)).inv G)) = ⊤
    rw [← Scheme.preimage_basicOpen_top]
    exact eq_top_iff.2 fun t _ => hgD t
  -- `L'` descends along `g`, so the `c_k` vanish on `T`
  have hc0 : ∀ k, φT (c k) = 0 := by
    intro k
    refine eq_zero_of_forall_exists_res_eq_zero _ fun t => ?_
    obtain ⟨U₁, htU₁, I, _, hfree⟩ := exists_free_of_descendsFromBase f' _ g hd' t
    obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open htU₁ U₁.isOpen
    refine ⟨W, htW, ?_⟩
    let φW : A →+* Γ(T, W) := (T.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.comp φT
    have hφW : Spec.map (CommRingCat.ofHom φW) = hW.fromSpec ≫ gT := by
      have h1 := IsAffineOpen.SpecMap_appLE_fromSpec gT (isAffineOpen_top (Spec (.of A))) hW
        (by simp)
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
      rw [← h1, ← Spec.map_comp]
      rfl
    let kW : pullback f' (hW.fromSpec ≫ g) ⟶ pullback f' ι :=
      pullback.lift (pullback.fst f' (hW.fromSpec ≫ g))
        (pullback.snd f' (hW.fromSpec ≫ g) ≫ hW.fromSpec ≫ gT)
        (by rw [Category.assoc, Category.assoc, hgT]; exact pullback.condition)
    have hsqW : IsPullback kW
        (pullback.snd f' (hW.fromSpec ≫ g)) f'A (Spec.map (CommRingCat.ofHom φW)) := by
      rw [hφW]
      exact isPullback_lift_comp f' ι (hW.fromSpec ≫ gT) (hW.fromSpec ≫ g)
        (by rw [Category.assoc, hgT])
    have hΓW := bijective_baseRingHom_of_isIso (pullback.snd f' (hW.fromSpec ≫ g)) (hfO' _)
    by_cases hY : Nonempty ((pullback f' (hW.fromSpec ≫ g) : Scheme.{u}) : Type u)
    · obtain ⟨y⟩ := hY
      obtain ⟨e⟩ := hfree hW.fromSpec (hW.fromSpec ≫ g) rfl (by rw [hW.range_fromSpec]; exact hWU)
      have hp' : kW ≫ q'A = pullback.fst f' (hW.fromSpec ≫ g) := pullback.lift_fst _ _ _
      obtain ⟨e2⟩ := nonempty_iso_unit_of_iso_free y _
        ((Scheme.Modules.pullback _).mapIso (Stacks.Cech.pullbackSquareIso i qA q'A aA haA' L) ≪≫
          (pullbackIsoOfComp kW q'A _ hp' _).symm ≪≫ e)
      exact hI _ φW (hφTG.map (T.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom) hsqW hΓW ⟨e2⟩ k
    · have : IsEmpty ((pullback f' (hW.fromSpec ≫ g) : Scheme.{u}) : Type u) :=
        not_nonempty_iff.1 hY
      have : Subsingleton Γ(T, W) := ⟨fun x y => hΓW.1 (Subsingleton.elim _ _)⟩
      exact Subsingleton.elim _ _
  -- so `L` is trivial on `X ×_S T`
  obtain ⟨eT⟩ := hIII Γ(T, ⊤) φT hφTG hc0
    (IsPullback.of_hasPullback fA (Spec.map (CommRingCat.ofHom φT)))
  let k₁ : pullback f g ⟶ pullback f ι := pullback.lift (pullback.fst f g)
    (pullback.snd f g ≫ gT) (by rw [Category.assoc, hgT]; exact pullback.condition)
  let k₂ : pullback f g ⟶ pullback fA (Spec.map (CommRingCat.ofHom φT)) :=
    pullback.lift k₁ (pullback.snd f g ≫ T.toSpecΓ) (by
      rw [Category.assoc, hφT]
      exact pullback.lift_snd _ _ _)
  have hk : k₂ ≫ pullback.fst fA (Spec.map (CommRingCat.ofHom φT)) ≫ qA = pullback.fst f g := by
    rw [← Category.assoc, pullback.lift_fst]
    exact pullback.lift_fst _ _ _
  exact descendsFromBase_of_nonempty_iso_unit f L g
    ⟨pullbackIsoOfComp k₂ _ _ hk L ≪≫
      (Scheme.Modules.pullback k₂).mapIso
        (((Scheme.Modules.pullbackComp (pullback.fst fA _) qA).app L).symm ≪≫ eT) ≪≫
      Scheme.Modules.pullbackUnitIso k₂⟩

/-- **Stacks Tag 0BF1, for given descent loci.** If `Z` and `Z'` represent the descent conditions
of `(f, L)` and `(f', i^* L)` in the sense of `AlgebraicGeometry.IsDescentLocus`, `s` lies in `Z`
and `H¹(X_s, 𝒪) → H¹(X'_s, 𝒪)` is injective, then a morphism with image in some open
neighbourhood `U` of `s` factors through `Z` exactly when it factors through `Z'`: that is,
`Z ∩ U = Z' ∩ U`. -/
theorem IsDescentLocus.exists_open_factorsThrough_iff {X X' S : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S} (i : X' ⟶ X) (hi : i ≫ f = f')
    [Flat f] [IsProper f] (hfp : FinitePresentation f)
    (hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    [Flat f'] [IsProper f'] (hfp' : FinitePresentation f')
    (hfO' : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f' a).toLRSHom.toShHom))
    {L : X.Modules} [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {Z Z' : Over S} (hZ : IsDescentLocus f L Z)
    (hZ' : IsDescentLocus f' ((Scheme.Modules.pullback i).obj L) Z') (s : S)
    (hs : ∃ h : Spec (S.residueField s) ⟶ Z.left, h ≫ Z.hom = S.fromSpecResidueField s)
    (hH1 : Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap
      (pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hi])
        (by rw [Category.comp_id, Category.id_comp])).toLRSHom.toShHom
      1 (SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) ≫
        (Stacks.Cohomology.moduleCohomologyAlong
          (pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id, hi])
            (by rw [Category.comp_id, Category.id_comp])).toLRSHom.toShHom 1).map
          (Scheme.Modules.pullbackUnitIso
            (pullback.map f' (S.fromSpecResidueField s) f (S.fromSpecResidueField s) i (𝟙 _)
              (𝟙 _) (by rw [Category.comp_id, hi])
              (by rw [Category.comp_id, Category.id_comp]))).hom)) :
    ∃ U : S.Opens, s ∈ U ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S), Set.range g.base ⊆ U →
      ((∃ h : T ⟶ Z.left, h ≫ Z.hom = g) ↔ (∃ h : T ⟶ Z'.left, h ≫ Z'.hom = g)) := by
  obtain ⟨U, hsU, hU⟩ := exists_open_descendsFromBase_iff f f' i hi hfp hfO hfp' hfO' L s
    ((hZ.factorsThrough_iff _).1 hs) hH1
  exact ⟨U, hsU, fun g hg => (hZ.factorsThrough_iff g).trans
    ((hU g hg).trans (hZ'.factorsThrough_iff g).symm)⟩

end AlgebraicGeometry

end
