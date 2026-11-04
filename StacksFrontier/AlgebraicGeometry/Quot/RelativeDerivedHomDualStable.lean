module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedHomSectionsNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomBijectiveOfHomologyIso
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimitHomStable
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The two stabilizations of the proof of Stacks 0DKY

Let `f' : X' ⟶ Y'` be a morphism of algebraic spaces.  Morphisms `A ⟶ E'` in `D(𝒪_{X'})` are
the global sections `𝒪_{Y'} ⟶ Rf'_* R𝓗om(A, E')` (Stacks 08JA and 0D6H), naturally in `A`, and
morphisms `A[1] ⟶ E'` are the maps `𝒪_{Y'}[1] ⟶ Rf'_* R𝓗om(A, E')`.  So if `u : A ⟶ A'`
induces a map `Rf'_* R𝓗om(A', E') ⟶ Rf'_* R𝓗om(A, E')` which is an isomorphism on cohomology in
degrees `≤ m`, `m ≥ 1`, then composing with `u` is bijective on `Hom(A', E')` and composing with
`u[1]` is surjective on `Hom(A'[1], E')`.  Along a derived colimit `K = hocolim Kₙ` whose
transition maps satisfy this from some index on (the window of the proof of Stacks 0DKY), the
coprojection `c_N` then induces a bijection `Hom(L(g')^*K, E') ≃ Hom(L(g')^*K_N, E')`.

On the dual side, if `c' : G ⟶ L` is an isomorphism on cohomology in degrees `> m` and
`m + 2 ≤ 0`, then composing with `Lq^* c'` is bijective on `Hom(Lq^*L, Lq^*𝒪)` for every
morphism `q`, because `Hom(Lq^*L, Lq^*𝒪) = Hom(L, Rq_* Lq^*𝒪)` and `Rq_* Lq^*𝒪 ∈ D^{≥ 0}`.

## Main results

* `AlgebraicGeometry.Space.homEquivStructureHomSheafHom_comp`: Stacks 08JA is natural in the
  source.
* `AlgebraicGeometry.Space.bijective_comp_of_isIso_homology_pushforward_sheafHom`: the
  per-morphism statement.
* `AlgebraicGeometry.Space.bijective_pull_coprojection_comp`: the stabilization along a derived
  colimit.
* `AlgebraicGeometry.Space.bijective_pull_coprojection_comp_structureObject`: the dual
  stabilization.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Morphisms as sections, naturally -/

/-- **Stacks 08JA is natural in the source**: under
`Hom(K, G) ≃ Hom(𝒪_X, R𝓗om(K, G))`, precomposition with `u : K' ⟶ K` is postcomposition with
`R𝓗om(u, G)`. -/
theorem homEquivStructureHomSheafHom_comp {X : AlgebraicSpaces B S hS}
    {K' K G : derivedModules B S hS X} (u : K' ⟶ K) (x : K ⟶ G) :
    homEquivStructureHomSheafHom B S hS K' G (u ≫ x) =
      homEquivStructureHomSheafHom B S hS K G x ≫
        ((smallEtaleDerivedSheafHom B S hS X).map u.op).app G :=
  Adjunction.homEquiv_comp_naturality_of_dinat (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction_dinaturality' X) (structureObject B S hS X)
    (smallEtaleDerivedLeftUnitIso B S hS) (smallEtaleDerivedLeftUnitIso_naturality X) u x

/-- Global sections on `X` are global sections of the direct image on `Y`:
`Hom(𝒪_X, Z) ≃ Hom(𝒪_Y, Rf_* Z)`, the adjunction `Lf^* ⊣ Rf_*` and `Lf^*𝒪_Y ≅ 𝒪_X`. -/
def structureHomPushEquiv {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (Z : derivedModules B S hS X) :
    (structureObject B S hS X ⟶ Z) ≃
      (structureObject B S hS Y ⟶ (spaceDerivedPushforward B S hS f).obj Z) :=
  ((smallEtaleDerivedPullStructureIso B S hS f).homCongr (Iso.refl Z)).symm.trans
    ((smallEtaleDerivedPullPushAdjunction B S hS f).homEquiv _ _)

/-- `AlgebraicGeometry.Space.structureHomPushEquiv` is natural in `Z`. -/
theorem structureHomPushEquiv_comp {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {Z Z' : derivedModules B S hS X} (x : structureObject B S hS X ⟶ Z) (w : Z ⟶ Z') :
    structureHomPushEquiv f Z' (x ≫ w) =
      structureHomPushEquiv f Z x ≫ (spaceDerivedPushforward B S hS f).map w := by
  simp only [structureHomPushEquiv, Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_symm, Iso.refl_hom, Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- Morphisms `A ⟶ E'` on `X` are global sections `𝒪_Y ⟶ Rf_* R𝓗om(A, E')`. -/
def structureHomSheafHomPushEquiv {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (A E : derivedModules B S hS X) :
    (A ⟶ E) ≃ (structureObject B S hS Y ⟶ (spaceDerivedPushforward B S hS f).obj
      (((smallEtaleDerivedSheafHom B S hS X).obj (op A)).obj E)) :=
  (homEquivStructureHomSheafHom B S hS A E).trans (structureHomPushEquiv f _)

/-- `AlgebraicGeometry.Space.structureHomSheafHomPushEquiv` is natural in the source. -/
theorem structureHomSheafHomPushEquiv_comp {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {A A' : derivedModules B S hS X} (u : A ⟶ A') (E : derivedModules B S hS X) (x : A' ⟶ E) :
    structureHomSheafHomPushEquiv f A E (u ≫ x) = structureHomSheafHomPushEquiv f A' E x ≫
      (spaceDerivedPushforward B S hS f).map
        (((smallEtaleDerivedSheafHom B S hS X).map u.op).app E) :=
  (congrArg (structureHomPushEquiv f _) (homEquivStructureHomSheafHom_comp u x)).trans
    (structureHomPushEquiv_comp f _ _)

/-- The commutation of `R𝓗om(-, E)` with the shift, on `D(𝒪_X)` as the target of the derived
pullback. -/
def smallEtaleDerivedSheafHomSourceShiftIso' (X : AlgebraicSpaces B S hS)
    (A E : derivedModules B S hS X) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (op (A⟦(1 : ℤ)⟧))).obj E ≅
      (((smallEtaleDerivedSheafHom B S hS X).obj (op A)).obj E)⟦(-1 : ℤ)⟧ :=
  smallEtaleDerivedSheafHomSourceShiftIso X A E

/-- `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomSourceShiftIso'` is natural. -/
theorem smallEtaleDerivedSheafHomSourceShiftIso'_naturality (X : AlgebraicSpaces B S hS)
    {A A' : derivedModules B S hS X} (u : A ⟶ A') (E : derivedModules B S hS X) :
    ((smallEtaleDerivedSheafHom B S hS X).map (u⟦(1 : ℤ)⟧').op).app E ≫
        (smallEtaleDerivedSheafHomSourceShiftIso' X A E).hom =
      (smallEtaleDerivedSheafHomSourceShiftIso' X A' E).hom ≫
        (((smallEtaleDerivedSheafHom B S hS X).map u.op).app E)⟦(-1 : ℤ)⟧' :=
  smallEtaleDerivedSheafHomSourceShiftIso_naturality X u E

/-! ### The stabilization along a derived colimit -/

/-- **Composition with a map which `Rf_* R𝓗om(-, E)` turns into an isomorphism in low
degrees.**  If `u : A ⟶ A'` in `D(𝒪_X)` induces a map `Rf_* R𝓗om(A', E) ⟶ Rf_* R𝓗om(A, E)`
which is an isomorphism on cohomology in degrees `≤ m`, `m ≥ 1`, then composing with `u` is
bijective on `Hom(A', E)` and composing with `u[1]` is bijective on `Hom(A'[1], E)`. -/
theorem bijective_comp_of_isIso_homology_pushforward_sheafHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {A A' : derivedModules B S hS X} (u : A ⟶ A') (E : derivedModules B S hS X)
    (m : ℤ) (hm : 1 ≤ m)
    (hu : ∀ i : ℤ, i ≤ m →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
        ((spaceDerivedPushforward B S hS f).map
          (((smallEtaleDerivedSheafHom B S hS X).map u.op).app E)))) :
    Function.Bijective (fun x : A' ⟶ E => u ≫ x) ∧
      Function.Bijective (fun x : A'⟦(1 : ℤ)⟧ ⟶ E => u⟦(1 : ℤ)⟧' ≫ x) :=
  Pretriangulated.bijective_comp_of_isIso_homology_sections (spaceDerivedPushforward B S hS f)
    (hR := spaceDerivedPushforwardCommShift f) ((smallEtaleDerivedSheafHom B S hS X).flip.obj E)
    E (structureObject B S hS Y) (fun A => structureHomSheafHomPushEquiv f A E)
    (fun u x => structureHomSheafHomPushEquiv_comp f u E x)
    (fun A => smallEtaleDerivedSheafHomSourceShiftIso' X A E)
    (fun u => smallEtaleDerivedSheafHomSourceShiftIso'_naturality X u E) u m hm hu

/-- **The stabilization of `Hom(L(g')^*K, E')` along a derived colimit** (step 1 of the
naturality of the proof of Stacks 0DKY).  Let `K = hocolim Kₙ` in `D(𝒪_X)`, let
`g' : X' ⟶ X` and `f' : X' ⟶ Y'`, and suppose that for every `n` the transition map induces a
map `Rf'_* R𝓗om(L(g')^*Kₙ₊₁, E') ⟶ Rf'_* R𝓗om(L(g')^*Kₙ, E')` which is an isomorphism on
cohomology in degrees `≤ a + n`.  Then for `a + N ≥ 1`, composing with `L(g')^* c_N` is a
bijection `Hom(L(g')^*K, E') ≃ Hom(L(g')^*K_N, E')`. -/
theorem bijective_pull_coprojection_comp {X X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (F : ℕ ⥤ derivedModules B S hS X) (K : derivedModules B S hS X)
    (c : ∀ n, F.obj n ⟶ K) [HasCoproduct F.obj] (hFK : IsHomotopyColimitWith F K c)
    (E' : derivedModules B S hS X') (a : ℤ)
    (hwin : ∀ (n : ℕ) (i : ℤ), i ≤ a + n →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map
        ((spaceDerivedPushforward B S hS f').map
          (((smallEtaleDerivedSheafHom B S hS X').map
            (((smallEtaleDerivedPullbackData B S hS).pull g').map
              (F.map (homOfLE (Nat.le_succ n)))).op).app E'))))
    (N : ℕ) (hN : 1 ≤ a + N) :
    Function.Bijective (fun x : ((smallEtaleDerivedPullbackData B S hS).pull g').obj K ⟶ E' =>
      ((smallEtaleDerivedPullbackData B S hS).pull g').map (c N) ≫ x) := by
  have hF' : HasCoproduct (F ⋙ (smallEtaleDerivedPullbackData B S hS).pull g').obj :=
    (hasColimitsOfShape_discrete_nat_derivedModules B S hS X').has_colimit _
  have : PreservesColimitsOfSize.{0, 0} ((smallEtaleDerivedPullbackData B S hS).pull g') :=
    (smallEtaleDerivedPullPushAdjunction B S hS g').leftAdjoint_preservesColimits
  have : ((smallEtaleDerivedPullbackData B S hS).pull g').IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS g'
  have h := hFK.map ((smallEtaleDerivedPullbackData B S hS).pull g')
  have key : ∀ n, N ≤ n → _ :=
    fun n hn => bijective_comp_of_isIso_homology_pushforward_sheafHom f' _ E' (a + n)
      (by omega) (hwin n)
  exact h.bijective_comp_of_stable E' N (fun n hn => (key n hn).1) fun n hn => (key n hn).2.2

/-! ### The dual stabilization -/

/-- **The stabilization of `Hom(Lq^*L, Lq^*𝒪)`** (step 7 of the naturality of the proof of
Stacks 0DKY).  If `c' : G ⟶ L` in `D(𝒪_Y)` is an isomorphism on cohomology in degrees `> m`
with `m + 2 ≤ 0`, then for every `q : T ⟶ Y` composing with `Lq^* c'` is a bijection
`Hom(Lq^*L, Lq^*𝒪_Y) ≃ Hom(Lq^*G, Lq^*𝒪_Y)`: by `Lq^* ⊣ Rq_*` it is composing with `c'` on
`Hom(-, Rq_* Lq^*𝒪_Y)`, and `Rq_* Lq^*𝒪_Y = Rq_* 𝒪_T` lies in `D^{≥ 0}`. -/
theorem bijective_pull_coprojection_comp_structureObject {T Y : AlgebraicSpaces B S hS}
    (q : T ⟶ Y) {G L : derivedModules B S hS Y} (c' : G ⟶ L) (m : ℤ) (hm : m + 2 ≤ 0)
    (hc : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map c')) :
    Function.Bijective (fun x : ((smallEtaleDerivedPullbackData B S hS).pull q).obj L ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull q).obj (structureObject B S hS Y) =>
      ((smallEtaleDerivedPullbackData B S hS).pull q).map c' ≫ x) := by
  have h0 : (((smallEtaleDerivedPullbackData B S hS).pull q).obj
      (structureObject B S hS Y)).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso (smallEtaleDerivedPullStructureIso B S hS q).symm 0
  have h1 := isGE_spaceDerivedPushforward_obj B S hS q _ 0 h0
  have e : (fun x : ((smallEtaleDerivedPullbackData B S hS).pull q).obj L ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull q).obj (structureObject B S hS Y) =>
      ((smallEtaleDerivedPullbackData B S hS).pull q).map c' ≫ x) =
      ((smallEtaleDerivedPullPushAdjunction B S hS q).homEquiv _ _).symm ∘
        (fun y => c' ≫ y) ∘ (smallEtaleDerivedPullPushAdjunction B S hS q).homEquiv _ _ := by
    funext x
    simp [← Adjunction.homEquiv_naturality_left]
  rw [e]
  exact (Equiv.bijective _).comp ((DerivedCategory.bijective_precomp_of_isIso_homologyMap_gt c' m hc
    _ 0 (by omega)).comp (Equiv.bijective _))

end AlgebraicGeometry.Space

end
