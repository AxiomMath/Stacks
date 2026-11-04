module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineCechCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCechVanishingAnyUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModuleAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineQuotientAux
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.CohomologyOverChartModules
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.CategoryTheory.Sites.Gerbe.ExistenceOfAnObject

/-!
# A gerbe over the spaces-étale site of an affine algebraic space has a global object

Let `X` be an affine algebraic space and `p : 𝒟 ⥤ X_{spaces,étale}` a gerbe over the spaces-étale
site of `X` (Stacks 03G0) whose band `𝒢` (Stacks 0CJY) has vanishing positive-degree Čech
cohomology on finite affine covering families of affine étale charts — which is what a
quasi-coherent band has. Then `p` has an object over the final object `X` of the site. This is
the cohomological half of the proof of Stacks 0CKI, read off Stacks 0CK0: the étale coverings of
`X` by affine objects are cofinal, their members and the fibre products of pairs of members are
affine, so `H¹` vanishes there, and `H²(X, 𝒢)` vanishes, all by the Čech criterion of Stacks 03F9
on the spaces-étale site
(`AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH'_of_isZero_cechCohomology`).

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.affineObjectChart`: the étale chart of `X` presented by an
  object of the spaces-étale site whose algebraic space is a scheme.
* `AlgebraicGeometry.Space.SpacesEtale.CechVanishing`: the Čech hypothesis of Stacks 03F9 on the
  spaces-étale site, read on the small étale site through the comparison of Stacks 03G1.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.mem_affineChartImages_iff`: an object of the spaces-étale
  site is, up to isomorphism, the image of an affine étale chart exactly when its algebraic space
  is affine.
* `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_pullback`: a fibre product of affine objects
  over an affine object is affine.
* `AlgebraicGeometry.Space.SpacesEtale.subsingleton_sheafH_over_of_isAffineSpace`: positive-degree
  cohomology over an affine object vanishes, given the Čech hypothesis.
* `AlgebraicGeometry.Space.SpacesEtale.nonempty_fiber_final_of_cechVanishing`: **a gerbe over the
  spaces-étale site of an affine algebraic space whose band satisfies the Čech hypothesis has an
  object over the final object.**
* `AlgebraicGeometry.Space.SpacesEtale.cechVanishing_of_iso_toSheaf`: the Čech hypothesis holds for
  every abelian sheaf isomorphic to the underlying sheaf of a quasi-coherent module on the ringed
  spaces-étale site.
* `AlgebraicGeometry.Space.SpacesEtale.cechVanishing_of_restriction_iso_toSheaf`: the Čech
  hypothesis holds for every abelian sheaf whose restriction to the small étale site (Stacks 03G1)
  is the underlying sheaf of a quasi-coherent `𝒪_X`-module, with sections in the universe of the
  étale charts.

## References

* [Stacks Project, Tag 0CK0](https://stacks.math.columbia.edu/tag/0CK0)
* [Stacks Project, Tag 0CKI](https://stacks.math.columbia.edu/tag/0CKI)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₂

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The slice of the small étale site at a chart has finite limits; local, as in
`StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineCechCriterion`, whose Čech hypothesis is
stated with this instance. -/
local instance hasFiniteLimits_overSmallEtaleChart' (W : SmallEtale B S hS X.1) :
    HasFiniteLimits (Over W) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- **The étale chart presented by an object of the spaces-étale site whose algebraic space is a
scheme.** For `i : U ≅ h_T`, the chart is `h_T → U → X`; it is étale because `U → X` is and
`i⁻¹` is an isomorphism. -/
def affineObjectChart (U : SpacesEtale B S hS X) {T : BigFppfOver B S hS}
    (i : U.obj.left.obj ≅ yoneda.obj T) : SmallEtale B S hS X.obj :=
  ⟨CostructuredArrow.mk (i.inv ≫ U.obj.hom.hom),
    U.property T i.inv (isEtaleChart_of_isIso B S hS T i.inv)⟩

/-- The comparison functor of Stacks 03G1 carries `affineObjectChart U i` back to `U`. -/
def comparisonFunctorObjAffineObjectChartIso (U : SpacesEtale B S hS X)
    {T : BigFppfOver B S hS} (i : U.obj.left.obj ≅ yoneda.obj T) :
    (comparisonFunctor B S hS X).obj (affineObjectChart U i) ≅ U :=
  ObjectProperty.isoMk _ (Over.isoMk (ObjectProperty.isoMk (P := IsAlgebraicSpace B S hS)
    (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (Y := U.obj.left) i.symm) rfl)

/-- **An object of the spaces-étale site is an affine chart image exactly when its algebraic
space is affine.** -/
theorem mem_affineChartImages_iff (U : SpacesEtale B S hS X) :
    U ∈ affineChartImages B S hS X ↔ IsAffineSpace B S hS U.obj.left.obj := by
  constructor
  · rintro ⟨V, hV, ⟨e⟩⟩
    exact ⟨(SmallEtale.toOver B S hS X.obj).obj V, hV,
      ⟨(ObjectProperty.ι _).mapIso ((toSpaces B S hS X).mapIso e)⟩⟩
  · rintro ⟨T, hT, ⟨i⟩⟩
    exact ⟨affineObjectChart U i, hT, ⟨(comparisonFunctorObjAffineObjectChartIso U i).symm⟩⟩

/-- **A fibre product of affine objects over an affine object of the spaces-étale site is
affine.** -/
theorem isAffineSpace_pullback {A A' C : SpacesEtale B S hS X} (f : A ⟶ C) (g : A' ⟶ C)
    (hA : IsAffineSpace B S hS A.obj.left.obj) (hA' : IsAffineSpace B S hS A'.obj.left.obj)
    (hC : IsAffineSpace B S hS C.obj.left.obj) :
    IsAffineSpace B S hS (pullback f g).obj.left.obj := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hC
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have sq : IsPullback ((toSpaces B S hS X).map (pullback.fst f g))
      ((toSpaces B S hS X).map (pullback.snd f g)) ((toSpaces B S hS X).map f)
      ((toSpaces B S hS X).map g) :=
    (IsPullback.of_hasPullback f g).map (toSpaces B S hS X)
  exact BeauvilleLaszlo.Space.isAffineSpace_of_isPullback_of_isSeparated sq hA hA'
    (ObjectProperty.isoMk _ e) inferInstance

/-- **The Čech hypothesis of Stacks 03F9 on the spaces-étale site**: the positive-degree Čech
cohomology of the restriction of `F` along the comparison functor of Stacks 03G1 vanishes on
every finite covering family of an affine étale chart by affine étale charts. -/
def CechVanishing (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ {W : SmallEtale B S hS X.1}, IsAffine (chartScheme W) →
    ∀ E : PreZeroHypercover.{u + 1} W, Finite E.I₀ →
      (∀ i, IsAffine (chartScheme (E.X i))) →
      E.sieve₀ ∈ SmallEtale.topology B S hS X.1 W →
      ∀ p : ℕ, 0 < p →
        IsZero (Stacks.CechSite.cechCohomology E ((comparisonFunctor B S hS X).op ⋙ F.obj) p)

/-- **Cohomology over an affine object vanishes in positive degrees**, for an abelian sheaf
satisfying the Čech hypothesis: Stacks 03F9 on the spaces-étale site, read on the slice. -/
theorem subsingleton_sheafH_over_of_isAffineSpace
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (hCech : CechVanishing F)
    (U : SpacesEtale B S hS X) (hU : IsAffineSpace B S hS U.obj.left.obj) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} (F.over U) q) := by
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  refine (Stacks.Cohomology.OverObjectCohomology.subsingleton_H_over_iff_subsingleton_H'.{u + 1}
    (topology B S hS X) U (extensionByZeroAdjunction B S hS X U) F q).2 ?_
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    (isZero_sheafH'_of_isZero_cechCohomology B S hS X F hCech U
      ((mem_affineChartImages_iff U).2 hU) q hq)

/-- Positive-degree Čech cohomology vanishing transfers along an isomorphism of presheaves. -/
private theorem isZero_cechCohomology_of_iso {W : SmallEtale B S hS X.1}
    {E : PreZeroHypercover.{u + 1} W} {P Q : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (e : P ≅ Q) {p : ℕ} (h : IsZero (Stacks.CechSite.cechCohomology E P p)) :
    IsZero (Stacks.CechSite.cechCohomology E Q p) :=
  h.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} _ p).mapIso
    ((Stacks.CechSite.cechComplexFunctor E).mapIso e)).symm

/-- **The Čech hypothesis is invariant under isomorphism of the coefficients.** -/
theorem CechVanishing.of_iso {F F' : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}}
    (e : F ≅ F') (hF : CechVanishing F) : CechVanishing F' := by
  intro W hW E hfin haff hcov p hp
  exact isZero_cechCohomology_of_iso (Functor.isoWhiskerLeft
    (comparisonFunctor B S hS X).op ((sheafToPresheaf _ _).mapIso e))
    (hF hW E hfin haff hcov p hp)

/-- **A quasi-coherent module on the ringed spaces-étale site satisfies the Čech hypothesis**,
and so does every abelian sheaf isomorphic to its underlying sheaf: this is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_comparisonCoefficients`. -/
theorem cechVanishing_of_iso_toSheaf
    (N : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O))
    (hN : N.IsQuasicoherentOnSite) (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (e : F ≅ (SheafOfModules.toSheaf _).obj N) : CechVanishing F :=
  CechVanishing.of_iso e.symm fun hW E hfin haff hcov p hp =>
    SmallEtale.isZero_cechCohomology_comparisonCoefficients B S hS X N hN hW E hfin haff hcov p hp

/-- **An abelian sheaf on `X_{spaces,étale}` which is a quasi-coherent `𝒪_X`-module satisfies the
Čech hypothesis.** Here "is a quasi-coherent `𝒪_X`-module" means that its restriction to the small
étale site along the comparison of Stacks 03G1 is the underlying abelian sheaf of a quasi-coherent
`𝒪_X`-module `M` (with sections in the universe of the étale charts), the reading of Stacks 0CKG
(2) recorded by `AlgebraicGeometry.Space.nonempty_iso_spacesEtaleAbelianSheaf_iff`. The Čech
vanishing for `M` is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_moduleCoefficients`. -/
theorem cechVanishing_of_restriction_iso_toSheaf
    (M : SheafOfModules.{u + 1} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (e : (spacesEtaleAbelianRestriction B S hS X).obj F ≅ (SheafOfModules.toSheaf _).obj M) :
    CechVanishing F := by
  intro W hW E hfin haff hcov p hp
  exact isZero_cechCohomology_of_iso (Q := (comparisonFunctor B S hS X).op ⋙ F.obj)
    ((sheafToPresheaf _ _).mapIso e).symm
    (SmallEtale.isZero_cechCohomology_moduleCoefficients B S hS X M hM hW E hfin haff hcov p hp)

/-- **A gerbe over the spaces-étale site of an affine algebraic space whose band satisfies the
Čech hypothesis has an object over the final object** (the cohomological half of the proof of
Stacks 0CKI, from Stacks 0CK0).

`p` is a gerbe — fibred in groupoids, a stack, locally nonempty, locally connected — and `𝒢`,
with its comparisons `θ`, is a band of `p` in the sense of Stacks 0CJY, stated with the three
clauses of `CategoryTheory.Gerbe.exists_sheaf_iso_morPresheaf_self_uliftFunctor_base`. The
covering families of `X` by affine objects are cofinal among all coverings
(`AlgebraicGeometry.Space.SpacesEtale.imageAffineCov_cofinal`), the fibre products of pairs of
their members are affine (`isAffineSpace_pullback`), and over all of these objects, as over `X`
itself, the positive-degree cohomology of `𝒢` vanishes
(`subsingleton_sheafH_over_of_isAffineSpace`); so conditions (1) and (2) of Stacks 0CK0 hold
at `X`. -/
theorem nonempty_fiber_final_of_cechVanishing {𝒟 : Type u₂} [Category.{u + 1} 𝒟]
    (p : 𝒟 ⥤ SpacesEtale B S hS X) (hp : p.IsFiberedInGroupoids)
    (hst : p.IsStack (topology B S hS X)) (hne : p.LocallyNonempty (topology B S hS X))
    (hlc : p.LocallyConnected (topology B S hS X))
    (𝒢 : Sheaf (topology B S hS X) CommGrpCat.{u + 1})
    (h𝒢 : haveI : p.IsFibered := hp.isFibered
      haveI : ∀ U : SpacesEtale B S hS X, IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid
      ∃ (θ : ∀ (U : SpacesEtale B S hS X) (y : p.Fiber U),
          (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
            p.morPresheaf y y ⋙ uliftFunctor.{u + 1, u + 1}),
        (∀ (U : SpacesEtale B S hS X) (y : p.Fiber U) (g : Over U)
            (a b : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) (a * b)).down =
              ((θ U y).hom.app (op g) a).down ≫ ((θ U y).hom.app (op g) b).down) ∧
          (∀ (U : SpacesEtale B S hS X) (y z : p.Fiber U) (φ : y ⟶ z) (g : Over U)
              (a : 𝒢.obj.obj (op g.left)),
            ((θ U z).hom.app (op g) a).down =
              Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
                ((θ U y).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom) ∧
          ∀ (U : SpacesEtale B S hS X) (y : p.Fiber U) (g : Over U)
            (a : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) a).down =
              (Functor.pullbackFiberIdIso (p.pullbackFiber y g.hom)).inv ≫
                ((θ g.left (p.pullbackFiber y g.hom)).hom.app
                  (op (Over.mk (𝟙 g.left))) a).down ≫
                  (Functor.pullbackFiberIdIso (p.pullbackFiber y g.hom)).hom)
    (hCech : CechVanishing
      ((sheafCompose (topology B S hS X) commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢))
    (hX : IsAffineSpace B S hS X.obj) :
    Nonempty (p.Fiber (final B S hS X)) := by
  let : p.IsFibered := hp.isFibered
  let : ∀ V : SpacesEtale B S hS X, IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid
  obtain ⟨θ, hmul, hconj, hbase⟩ := h𝒢
  let G := (sheafCompose (topology B S hS X) commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢
  have hfin : IsAffineSpace B S hS (final B S hS X).obj.left.obj := hX
  let Cov : Set (PreZeroHypercover.{u + 1} (final B S hS X)) :=
    {E | E.sieve₀ ∈ topology B S hS X (final B S hS X) ∧
      ∀ i, IsAffineSpace B S hS (E.X i).obj.left.obj}
  refine CategoryTheory.Gerbe.nonempty_fiber_of_cohomology_vanishing (topology B S hS X) p hp hst
    hne hlc G
    ⟨θ, fun V y g a b => hmul V y g (Multiplicative.ofAdd a) (Multiplicative.ofAdd b),
      fun V y z φ g a => hconj V y z φ g (Multiplicative.ofAdd a),
      fun V y g a => hbase V y g (Multiplicative.ofAdd a)⟩
    (final B S hS X) Cov (fun E hE => hE.1) ?_ (fun _ _ _ _ => inferInstance)
    (fun E hE i => subsingleton_sheafH_over_of_isAffineSpace G hCech (E.X i) (hE.2 i) 1 one_pos)
    (fun E hE i j => subsingleton_sheafH_over_of_isAffineSpace G hCech _
      (isAffineSpace_pullback (E.f i) (E.f j) (hE.2 i) (hE.2 j) hfin) 1 one_pos)
    (subsingleton_sheafH_over_of_isAffineSpace G hCech _ hfin 2 two_pos)
  intro R hR
  obtain ⟨E, hE, hle⟩ := imageAffineCov_cofinal B S hS X G hCech (final B S hS X)
    ((mem_affineChartImages_iff _).2 hfin) R hR
  exact ⟨E.1, ⟨E.2, fun i => (mem_affineChartImages_iff _).1 (hE.2.1 i)⟩, hle⟩

end AlgebraicGeometry.Space.SpacesEtale

end
