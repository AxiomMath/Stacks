module

public import StacksFrontier.AlgebraicGeometry.Spaces.StrictHenselizationClosedPointStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a direct image at a geometric point, over the strict henselization

Let `S` be a scheme, `X` an algebraic space over `S`, `f : Y ⟶ X` a quasi-compact and
quasi-separated morphism, `x̄` a geometric point of `X` and `h : Spec(𝒪_{X, x̄}) ⟶ X` the
canonical morphism.  **Stacks 0AES** asserts that for a quasi-coherent `𝒪_Y`-module `𝒢`

`(f_*𝒢)_{x̄} = Γ(Y ×_X Spec(𝒪_{X, x̄}), p^*𝒢)`,

where `p : Y ×_X Spec(𝒪_{X, x̄}) ⟶ Y` is the projection.  The source prints `p^*𝓕`; the only
module in the statement is `𝒢`, so `𝓕` is a misprint for `𝒢`, and `p^*𝒢` is what is formalized.

## Main definitions

* `AlgebraicGeometry.Space.strictHenselizationSpace` and
  `AlgebraicGeometry.Space.strictHenselizationSpaceHom`: `Spec(𝒪_{X, x̄})` as an algebraic space
  over `S` and its canonical morphism to `X`, which is
  `AlgebraicGeometry.Space.strictHenselizationToSpace` (Stacks 04KG, 04KF).
* `AlgebraicGeometry.Space.strictHenselizationFlatBaseChangeIso`: the base change isomorphism
  `h^*f_*𝒢 ≅ f'_*p^*𝒢` of Stacks 073K, part (1), in degree zero.
* `AlgebraicGeometry.Space.directImageGeometricStalkAddEquiv`: the identification
  `(f_*𝒢)_{x̄} ≃+ Γ(Y ×_X Spec(𝒪_{X, x̄}), p^*𝒢)` (Stacks 0AES).

## Proof

The stalk at `x̄` of any `𝒪_X`-module `ℳ` is `Γ(Spec(𝒪_{X, x̄}), h^*ℳ)`: by Stacks 05VQ the stalk
of `h^*ℳ` at the closed point `t̄` is `𝒪_{T, t̄} ⊗_{𝒪_{X, x̄}} ℳ_{x̄}`, the homomorphism
`𝒪_{X, x̄} ⟶ 𝒪_{T, t̄}` is bijective
(`AlgebraicGeometry.Space.bijective_etaleLocalRingMap_strictHenselizationToSpace`), and over the
strictly henselian `T` the stalk at `t̄` is the module of global sections
(`AlgebraicGeometry.Space.isInitialStrictHenselizationIdNeighborhood`).  For `ℳ = f_*𝒢` the
morphism `h` is flat (`AlgebraicGeometry.Space.isFlat_strictHenselizationToSpace`), so Stacks
073K, part (1), in degree zero gives `h^*f_*𝒢 ≅ f'_*p^*𝒢` for the base change `f'` of `f`, and
global sections of a direct image are global sections upstairs.

## References

* [Stacks Project, Tag 0AES](https://stacks.math.columbia.edu/tag/0AES)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Two transports -/

variable (B S hS) in
/-- The global sections of an `𝒪_X`-module are its sections over a terminal étale chart: a
compatible family is the family of restrictions of its value there. -/
def moduleSectionsAddEquivOfIsTerminal {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, m} B S hS X.1 X.2) {V : SmallEtale B S hS X.1} (hV : IsTerminal V) :
    M.sections ≃+ M.val.obj (op V) where
  toFun s := s.eval (op V)
  invFun a := ⟨fun W => M.val.map (hV.from W.unop).op a, fun {W _} g =>
    (PresheafOfModules.map_comp_apply M.val (hV.from W.unop).op g a).symm.trans
      (PresheafOfModules.congr_map_apply M.val (Quiver.Hom.unop_inj (hV.hom_ext _ _)) a)⟩
  left_inv s := Subtype.ext (funext fun W => s.2 (hV.from W.unop).op)
  right_inv a :=
    (PresheafOfModules.congr_map_apply M.val
      (congrArg Quiver.Hom.op (hV.hom_ext (hV.from V) (𝟙 V))) a).trans
      (congrArg (fun k : M.val.presheaf.obj (op V) ⟶ M.val.presheaf.obj (op V) =>
        ConcreteCategory.hom k a) (M.val.presheaf.map_id (op V)))
  map_add' _ _ := rfl

variable (B S hS) in
/-- Equal geometric points have the same stalks. -/
def geometricModuleStalkAddEquivOfEq (X : AlgebraicSpaces B S hS)
    {y z : GeometricPoint B S hS X.1} (h : y = z) (M : Modules.{u, m} B S hS X.1 X.2) :
    geometricModuleStalk B S hS X y M ≃+ geometricModuleStalk B S hS X z M := by
  subst h
  exact AddEquiv.refl _

/-! ### The strict henselization as an algebraic space -/

/-- **The strict henselization `Spec(𝒪_{X, x̄})` of an algebraic space at a geometric point**, as
an algebraic space over `S`: the represented presheaf of
`AlgebraicGeometry.Space.strictHenselizationObj`. -/
abbrev strictHenselizationSpace (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1) :
    AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (strictHenselizationObj X.2 x), isAlgebraicSpace_yoneda B S hS _⟩

/-- **The canonical morphism `Spec(𝒪_{X, x̄}) ⟶ X`** of Stacks 04KG, as a morphism of algebraic
spaces. -/
abbrev strictHenselizationSpaceHom (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1) :
    strictHenselizationSpace X x ⟶ X :=
  ObjectProperty.homMk (strictHenselizationToSpace X.2 x)

/-! ### Flat base change along `Spec(𝒪_{X, x̄}) ⟶ X` in degree zero -/

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hqc : IsQuasiCompact B S hS f.hom)
  (hqs : IsQuasiSeparated B S hS f.hom) (x : GeometricPoint B S hS X.1)
  (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite)

/-- **Stacks 073K, part (1), in degree zero, along `h : Spec(𝒪_{X, x̄}) ⟶ X`**: for the cartesian
square with `p : Y ×_X Spec(𝒪_{X, x̄}) ⟶ Y` and `f' : Y ×_X Spec(𝒪_{X, x̄}) ⟶ Spec(𝒪_{X, x̄})`,
`h^*f_*𝒢 ≅ f'_*p^*𝒢`.  The morphism `h` is flat. -/
def strictHenselizationFlatBaseChangeIso :
    (modulePullback B S hS (strictHenselizationSpaceHom X x)).obj
        ((modulePushforward B S hS f).obj G) ≅
      (modulePushforward B S hS (pullback.snd f (strictHenselizationSpaceHom X x))).obj
        ((modulePullback B S hS (pullback.fst f (strictHenselizationSpaceHom X x))).obj G) :=
  haveI := modulePushforward_additive B S hS f
  haveI := modulePushforward_additive B S hS (pullback.snd f (strictHenselizationSpaceHom X x))
  haveI : PreservesFiniteLimits (modulePushforward B S hS
      (pullback.snd f (strictHenselizationSpaceHom X x))) :=
    haveI : PreservesLimitsOfSize.{0, 0} (modulePushforward B S hS
        (pullback.snd f (strictHenselizationSpaceHom X x))) :=
      (modulePullbackAdjunction B S hS
        (pullback.snd f (strictHenselizationSpaceHom X x))).rightAdjoint_preservesLimits
    PreservesLimitsOfSize.preservesFiniteLimits _
  (modulePullback B S hS (strictHenselizationSpaceHom X x)).mapIso
      ((modulePushforward B S hS f).rightDerivedZeroIsoSelf.app G).symm ≪≫
    @asIso _ _ _ _ _ (isIso_higherDirectImageBaseChangeMap_of_isFlat
      (IsPullback.of_hasPullback f (strictHenselizationSpaceHom X x))
      (isFlat_strictHenselizationToSpace X.2 x) hqc hqs G hG 0) ≪≫
    (modulePushforward B S hS
      (pullback.snd f (strictHenselizationSpaceHom X x))).rightDerivedZeroIsoSelf.app _

/-! ### Stacks 0AES -/

/-- **The stalk of a direct image at a geometric point, over the strict henselization.**  Let `X`
be an algebraic space over `S`, `f : Y ⟶ X` a quasi-compact and quasi-separated morphism, `x̄` a
geometric point of `X` and `h : Spec(𝒪_{X, x̄}) ⟶ X` the canonical morphism
(`AlgebraicGeometry.Space.strictHenselizationSpaceHom`).  For a quasi-coherent `𝒪_Y`-module `𝒢`,

`(f_*𝒢)_{x̄} = Γ(Y ×_X Spec(𝒪_{X, x̄}), p^*𝒢)`,

where `p : Y ×_X Spec(𝒪_{X, x̄}) ⟶ Y` is the projection: the geometric stalk of the direct image
is identified, as an abelian group, with the global sections of the pullback of `𝒢` to the base
change of `Y` to the strict henselization.  (The source prints `p^*𝓕` for `p^*𝒢`.)

The identification is the composite of: the stalk of `f_*𝒢` at `x̄ = h ∘ t̄` with the stalk of
`h^*f_*𝒢` at the closed point `t̄` (Stacks 05VQ and the bijectivity of
`𝒪_{X, x̄} ⟶ 𝒪_{T, t̄}`), that stalk with the global sections of `h^*f_*𝒢` (the closed point has an
initial neighbourhood), the flat base change `h^*f_*𝒢 ≅ f'_*p^*𝒢` of Stacks 073K, and
`Γ(T, f'_* -) = Γ(Y ×_X T, -)`. -/
@[stacks 0AES "(f_*G)_xbar = Γ(Y ×_X Spec(O_{X,xbar}), p^*G) for f quasi-compact and
  quasi-separated and G quasi-coherent, as an isomorphism of abelian groups; the source's p^*F is
  a misprint for p^*G"]
def directImageGeometricStalkAddEquiv :
    geometricModuleStalk B S hS X x ((modulePushforward B S hS f).obj G) ≃+
      ((modulePullback B S hS (pullback.fst f (strictHenselizationSpaceHom X x))).obj
        G).sections :=
  (geometricModuleStalkAddEquivOfEq B S hS X
      (geometricPointMap_strictHenselizationGeometricPoint X.2 x) _).symm.trans <|
  (ModuleCat.extendScalarsRingEquivAddEquiv (RingEquiv.ofBijective _
      (bijective_etaleLocalRingMap_strictHenselizationToSpace X.2 x)) _).trans <|
  (geometricModuleStalkPullbackIso B S hS (strictHenselizationSpaceHom X x)
      (strictHenselizationGeometricPoint X.2 x)
      ((modulePushforward B S hS f).obj G)).symm.toLinearEquiv.toAddEquiv.trans <|
  (AddEquiv.ofBijective (geometricModuleStalkGerm B S hS (strictHenselizationSpace X x)
      (strictHenselizationGeometricPoint X.2 x) _ (strictHenselizationIdNeighborhood X.2 x))
      (bijective_geometricModuleStalkGerm_of_isInitial B S hS _ _ _
        (isInitialStrictHenselizationIdNeighborhood X.2 x))).symm.trans <|
  (moduleSectionsAddEquivOfIsTerminal B S hS _
      (isTerminal_idChart B S hS (strictHenselizationObj X.2 x))).symm.trans <|
  ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (strictHenselizationSpace X x).1
          (strictHenselizationSpace X x).2).O)).mapIso
      (strictHenselizationFlatBaseChangeIso f hqc hqs x G hG)).toLinearEquiv.toAddEquiv.trans <|
  ((globalSectionsModulePushforwardIso B S hS
      (pullback.snd f (strictHenselizationSpaceHom X x))).app _).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.Space

end
