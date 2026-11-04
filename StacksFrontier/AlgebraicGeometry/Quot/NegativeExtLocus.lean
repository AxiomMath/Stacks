module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesFibreExtBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCartesianPullback
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.EtalePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentPullbackRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom

/-!
# The locus of vanishing negative fibre extensions (statements of Stacks 0DLC)

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over a
scheme `S`, let `K` be a pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`.  Stacks 0DLC
says:

1. there is an open `W ⊆ Y` characterized by: a point `y : Spec(k) ⟶ Y` with values in a field
   lies in `|W|` if and only if `Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for all `i < 0`;
2. for every `V ⟶ Y` factoring through `W`, `Ext^i_{𝒪_{X_V}}(K_V, E_V) = 0` for all `i < 0`;
3. the functor `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` on the schemes over `W` is an algebraic space affine
   and of finite presentation over `W`.

Its proof rests on Stacks 0DKY, which is not in the library.  This file states the three parts,
in the vocabulary of `StacksFrontier/AlgebraicGeometry/Quot/ComplexesFibreExtBaseChange.lean` and
`StacksFrontier/AlgebraicGeometry/Quot/RelativeDerivedHomFunctor.lean`, together with the content of
Stacks 0DKY, so that the consumers of Stacks 0DLC (Stacks 0DLD, 0DLG, 0DLJ, 0DLM) can carry them
as hypotheses, and proves the reduction of part (2) to the case `W = Y` that the source makes.
Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.HasNoNegativeExtAt`: `Ext^i(K_y, E_y) = 0` for `i < 0` at a test
  scheme `y` over `Y`.
* `AlgebraicGeometry.Space.IsNegativeExtLocus`: the property characterizing the open of part (1).
* `AlgebraicGeometry.Space.ExistsNegativeExtLocus`,
  `NegativeExtVanishesOverLocus` and `RelativeDerivedHomRepresentableOverLocus`: the three parts
  of Stacks 0DLC, as propositions.
* `AlgebraicGeometry.Space.NegativeExtVanishesOfFibres` and
  `RelativeDerivedHomRepresentableOfFibres`: parts (2) and (3) in the case `W = Y`, to which the
  source reduces them.
* `AlgebraicGeometry.Space.RelativeDerivedHomDualExists`: the content of Stacks 0DKY.
* `AlgebraicGeometry.Space.RelativelyPerfectBaseChangeStable`: the content of Stacks 0DKT.

## Main results

* `AlgebraicGeometry.Space.hasNoNegativeFieldFibreExt_iff`: condition (2) of Stacks 0DLD is the
  vanishing at every field point with `K = E`.
* `AlgebraicGeometry.Space.isNegativeExtLocus_top`: if the negative fibre extensions vanish at
  every field point, the whole space is a locus of part (1).
* `AlgebraicGeometry.Space.NegativeExtVanishesOverLocus.negativeExtVanishesOfFibres`: part (2)
  gives its case `W = Y`.
* `AlgebraicGeometry.Space.NegativeExtVanishesOfFibres.negativeExtVanishesOverLocus`: conversely,
  as in the source, the case `W = Y` of part (2) gives part (2).
* `AlgebraicGeometry.Space.IsNegativeExtLocus.hasNoNegativeExtAt_restrict`: over a locus `W`, the
  negative fibre extensions of the restrictions `K_W`, `E_W` vanish at every field point of `W`.

## Implementation notes

A point `y : Spec(k) ⟶ Y` with values in a field is a test scheme `T₀` over `Y` whose underlying
scheme is the spectrum of a field, `AlgebraicGeometry.Stack.IsFieldObject`, as in
`AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt`; it lies in `|W|` when its section
`AlgebraicGeometry.Space.testPoint` of `Y` lies in the subfunctor `W`.  `Ext^i(K_y, E_y)` is the
group of morphisms `K_y ⟶ E_y⟦i⟧`, and its vanishing is written as a `Subsingleton`.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Locus

variable {X Y : AlgebraicSpaces B S hS}

/-- **`Ext^i(K_y, E_y) = 0` for `i < 0` at a test scheme over `Y`.**  For `f : X ⟶ Y`, objects `K`,
`E` of `D(𝒪_X)` and a test scheme `y : T₀ ⟶ Y`, the negative extensions between the derived
pullbacks `K_y`, `E_y` of `K`, `E` along the projection `X_y = X ×_Y T₀ ⟶ X` vanish. -/
def HasNoNegativeExtAt (f : X ⟶ Y) (K E : derivedModules B S hS X) (T₀ : SchemesOver Y) : Prop :=
  ∀ i : ℤ, i < 0 →
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj K ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj E)⟦i⟧)

/-- Condition (2) of Stacks 0DLD is the vanishing of the negative fibre extensions at every point
with values in a field, with `K = E`. -/
theorem hasNoNegativeFieldFibreExt_iff (f : X ⟶ Y) (E : derivedModules B S hS X) :
    HasNoNegativeFieldFibreExt f E ↔
      ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f E E T₀ :=
  Iff.rfl

/-- **The property characterizing the open of Stacks 0DLC, part (1).**  An open subspace `W` of
`Y` is a locus of vanishing negative fibre extensions of `K` and `E` when a point
`y : Spec(k) ⟶ Y` with values in a field lies in `|W|` if and only if
`Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for all `i < 0`. -/
def IsNegativeExtLocus (f : X ⟶ Y) (K E : derivedModules B S hS X)
    (W : OpenSubspaces B S hS Y.1) : Prop :=
  ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left →
    (testPoint T₀ ∈ W.1.obj (Opposite.op T₀.left) ↔ HasNoNegativeExtAt f K E T₀)

/-- The whole space as an open subspace of itself. -/
abbrev topOpenSubspace (Y : AlgebraicSpaces B S hS) : OpenSubspaces B S hS Y.1 :=
  ⟨⊤, isOpenSubspace_top Y.2⟩

/-- If the negative fibre extensions of `K` and `E` vanish at every point with values in a field,
the whole space is a locus of part (1) of Stacks 0DLC. -/
theorem isNegativeExtLocus_top (f : X ⟶ Y) (K E : derivedModules B S hS X)
    (h : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀) :
    IsNegativeExtLocus f K E (topOpenSubspace Y) :=
  fun T₀ hT₀ => ⟨fun _ => h T₀ hT₀, fun _ => trivial⟩

/-- On a locus of part (1) of Stacks 0DLC which is the whole space, the negative fibre extensions
vanish at every point with values in a field. -/
theorem IsNegativeExtLocus.hasNoNegativeExtAt_of_top {f : X ⟶ Y} {K E : derivedModules B S hS X}
    (h : IsNegativeExtLocus f K E (topOpenSubspace Y)) (T₀ : SchemesOver Y)
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) : HasNoNegativeExtAt f K E T₀ :=
  (h T₀ hT₀).1 trivial

/-- **The functor `V ↦ Hom(K_V, E_V)` on the test schemes over an open subspace `W` of `Y`**: the
relative derived Hom functor of `AlgebraicGeometry.Space.relativeDerivedHom`, at the test schemes
over `W` regarded as test schemes over `Y`. -/
def relativeDerivedHomOverOpen (f : X ⟶ Y) (K E : derivedModules B S hS X)
    (W : OpenSubspaces B S hS Y.1) :
    (SchemesOver (openSubspaceAsSpace B S hS W))ᵒᵖ ⥤ Type (u + 1) :=
  (CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
    (openSubspaceImmersion B S hS W)).op ⋙ relativeDerivedHom f K E

end Locus

/-! ### The three parts of Stacks 0DLC -/

section Statements

variable (B S hS)

/-- **Stacks 0DLC, part (1)**, as a proposition: for every proper, flat, finitely presented
morphism `f : X ⟶ Y` of algebraic spaces, every pseudo-coherent `K` and every `Y`-perfect `E` in
`D(𝒪_X)`, there is an open `W ⊆ Y` with `y ∈ |W| ⟺ Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for `i < 0`, for
every point `y : Spec(k) ⟶ Y` with values in a field. -/
def ExistsNegativeExtLocus : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      ∃ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W

/-- **Stacks 0DLC, part (2)**, as a proposition: in the situation of part (1), for every open `W`
characterized as there and every algebraic space `V` over `Y` whose morphism to `Y` factors
through `W`, `Ext^i_{𝒪_{X_V}}(K_V, E_V) = 0` for `i < 0`. -/
def NegativeExtVanishesOverLocus : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      ∀ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W →
      ∀ V : Over Y, (∃ g : V.left ⟶ openSubspaceAsSpace B S hS W,
          g ≫ openSubspaceImmersion B S hS W = V.hom) →
      ∀ i : ℤ, i < 0 →
        Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)

/-- **Stacks 0DLC, part (3)**, as a proposition: in the situation of part (1), for every open `W`
characterized as there, the functor `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` on the schemes over `W` is an
algebraic space affine and of finite presentation over `W`.  (Being representable, it is in
particular a sheaf.) -/
def RelativeDerivedHomRepresentableOverLocus : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      ∀ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W →
      IsAffineFinitePresentationAlgebraicSpaceOver (openSubspaceAsSpace B S hS W)
        (relativeDerivedHomOverOpen f K E W)

/-- **Stacks 0DLC, part (2), in the case `W = Y`**, to which the source reduces it: if the
negative fibre extensions of `K` and `E` vanish at every point with values in a field, then
`Ext^i_{𝒪_{X_V}}(K_V, E_V) = 0` for `i < 0` for every algebraic space `V` over `Y`. -/
def NegativeExtVanishesOfFibres : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀) →
      ∀ (V : Over Y) (i : ℤ), i < 0 →
        Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)

/-- **Stacks 0DLC, part (3), in the case `W = Y`**, to which the source reduces it: if the
negative fibre extensions of `K` and `E` vanish at every point with values in a field, then the
functor `T ↦ Hom_{𝒪_{X_T}}(K_T, E_T)` on the schemes over `Y` is an algebraic space affine and of
finite presentation over `Y`. -/
def RelativeDerivedHomRepresentableOfFibres : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀) →
      IsAffineFinitePresentationAlgebraicSpaceOver Y (relativeDerivedHom f K E)

/-- Part (2) of Stacks 0DLC gives its case `W = Y`: the whole space is a locus, and every
algebraic space over `Y` factors through it. -/
theorem NegativeExtVanishesOverLocus.negativeExtVanishesOfFibres
    (h : NegativeExtVanishesOverLocus B S hS) : NegativeExtVanishesOfFibres B S hS := by
  intro X Y f hp hflat hfp K E hK hE hfib V i hi
  have hle : Subfunctor.range V.hom.hom ≤ (topOpenSubspace Y).1 := fun _ _ _ => trivial
  exact h f hp hflat hfp K E hK hE (topOpenSubspace Y) (isNegativeExtLocus_top f K E hfib) V
    ⟨ObjectProperty.homMk (Subfunctor.lift V.hom.hom hle),
      ObjectProperty.hom_ext _ (Subfunctor.lift_ι V.hom.hom hle)⟩ i hi

/-! ### The content of Stacks 0DKY -/

/-- **The content of Stacks 0DKY** (not yet proved here), as a proposition: for a
morphism `f : X ⟶ Y` of algebraic spaces with `Y` quasi-compact and quasi-separated and `f`
proper, flat and of finite presentation, a `Y`-perfect `E` and a pseudo-coherent `K` in
`D(𝒪_X)`, there is a pseudo-coherent `L` in `D(𝒪_Y)` with
`Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`, and the same after every cartesian base change
`X' = X ×_Y Y'`: `Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{Y'})`. -/
def RelativeDerivedHomDualExists : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
    IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      ∃ L : derivedModules B S hS Y, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L ∧
        Nonempty ((spaceDerivedPushforward B S hS f).obj
            (((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op K)).obj E) ≅
          smallEtaleDerivedDual B S hS Y L) ∧
        ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
          IsPullback g' f' f g →
          Nonempty ((spaceDerivedPushforward B S hS f').obj
              (((smallEtaleDerivedSheafHom B S hS X').obj
                (Opposite.op (((smallEtaleDerivedPullbackData B S hS).pull g').obj K))).obj
                  (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) ≅
            smallEtaleDerivedDual B S hS Y' (((smallEtaleDerivedPullbackData B S hS).pull g).obj L))

end Statements

/-! ### The reduction of part (2) to the case `W = Y` -/

section Reduction

variable (B S hS) in
/-- **The content of Stacks 0DKT** (not yet proved here), as a proposition: for a flat,
locally finitely presented morphism `f : X ⟶ Y` of algebraic spaces, a morphism `g : Y' ⟶ Y` and
the cartesian square `X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, the
derived pullback `L(g')^*E` of a `Y`-perfect `E` is `Y'`-perfect. -/
def RelativelyPerfectBaseChangeStable : Prop :=
  ∀ {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback g' f' f g →
    ∀ (hflat : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
      (hflat' : IsFlat B S hS f'.hom) (hlfp' : IsLocallyOfFinitePresentation B S hS f'.hom)
      (E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hlfp E →
      IsPerfectRelativeToCanonical B S hS f' hflat' hlfp'
        (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)

/-- The vanishing of the morphisms `M ⟶ N⟦i⟧` transports along isomorphisms of `M` and `N`. -/
theorem subsingleton_hom_shift_congr {C : Type*} [Category* C] [HasShift C ℤ] {M M' N N' : C}
    (eM : M ≅ M') (eN : N ≅ N') (i : ℤ) :
    Subsingleton (M ⟶ N⟦i⟧) ↔ Subsingleton (M' ⟶ N'⟦i⟧) :=
  (eM.homCongr ((shiftFunctor C i).mapIso eN)).subsingleton_congr

/-- The negative extensions between two derived pullbacks along a composite `p ≫ r` are those
between the iterated derived pullbacks, by the composition comparison of Stacks 0D6D. -/
theorem subsingleton_pull_comp_iff {Z X' X : AlgebraicSpaces B S hS} (p : Z ⟶ X') (r : X' ⟶ X)
    (M N : derivedModules B S hS X) (i : ℤ) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull p).obj
        (((smallEtaleDerivedPullbackData B S hS).pull r).obj M) ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull p).obj
        (((smallEtaleDerivedPullbackData B S hS).pull r).obj N))⟦i⟧) ↔
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (p ≫ r)).obj M ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (p ≫ r)).obj N)⟦i⟧) :=
  subsingleton_hom_shift_congr (((smallEtaleDerivedPullbackData B S hS).compIso p r).app M).symm
    (((smallEtaleDerivedPullbackData B S hS).compIso p r).app N).symm i

/-- The negative extensions between two derived pullbacks do not change when the morphism is
precomposed with an isomorphism of algebraic spaces: the derived pullback along an isomorphism
is an equivalence commuting with the shift. -/
theorem subsingleton_pull_iff_of_iso {Z Z' X : AlgebraicSpaces B S hS} (φ : Z ≅ Z')
    {p : Z' ⟶ X} {q : Z ⟶ X} (hq : φ.hom ≫ p = q) (M N : derivedModules B S hS X) (i : ℤ) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull p).obj M ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull p).obj N)⟦i⟧) ↔
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull q).obj M ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull q).obj N)⟦i⟧) := by
  let P := smallEtaleDerivedPullbackData B S hS
  let F := (P.pullEquivalence φ).functor
  have : F.CommShift ℤ := smallEtaleDerivedPullbackData_pull_commShift φ.hom
  let e : ((P.pull p).obj M ⟶ ((P.pull p).obj N)⟦i⟧) ≃
      (F.obj ((P.pull p).obj M) ⟶ (F.obj ((P.pull p).obj N))⟦i⟧) :=
    (P.pullEquivalence φ).fullyFaithfulFunctor.homEquiv.trans
      ((Iso.refl _).homCongr ((F.commShiftIso i).app ((P.pull p).obj N)))
  exact e.subsingleton_congr.trans (subsingleton_hom_shift_congr
    ((P.triangle hq).app M).symm ((P.triangle hq).app N).symm i)

variable {X Y : AlgebraicSpaces B S hS}

/-- A test scheme over an open subspace `W` of `Y`, read as a test scheme over `Y`, lies in
`|W|`. -/
theorem testPoint_map_mem (W : OpenSubspaces B S hS Y.1)
    (T₀ : SchemesOver (openSubspaceAsSpace B S hS W)) :
    testPoint ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
      (openSubspaceImmersion B S hS W)).obj T₀) ∈ W.1.obj (Opposite.op T₀.left) := by
  have h : testPoint ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
      (openSubspaceImmersion B S hS W)).obj T₀) = W.1.ι.app _ (testPoint T₀) :=
    yonedaEquiv_comp T₀.hom.hom W.1.ι
  rw [h]
  exact (testPoint T₀).2

/-- **The restriction to a locus.**  Let `W` be a locus of part (1) of Stacks 0DLC for `f`, `K`,
`E`, let `X_W ⟶ W` be the base change of `f` to `W` and `K_W`, `E_W` the derived pullbacks of `K`,
`E` to `X_W`.  Then the negative fibre extensions of `K_W` and `E_W` vanish at every point of `W`
with values in a field: such a point is a point of `Y` lying in `|W|`, and its fibre in `X_W` is
its fibre in `X`, by pasting the two cartesian squares. -/
theorem IsNegativeExtLocus.hasNoNegativeExtAt_restrict {f : X ⟶ Y} {K E : derivedModules B S hS X}
    {W : OpenSubspaces B S hS Y.1} (hW : IsNegativeExtLocus f K E W)
    (T₀ : SchemesOver (openSubspaceAsSpace B S hS W)) (hT₀ : Stack.IsFieldObject B S hS T₀.left) :
    HasNoNegativeExtAt (overInclusion f (Over.mk (openSubspaceImmersion B S hS W)))
      (((smallEtaleDerivedPullbackData B S hS).pull
        (overProjection f (Over.mk (openSubspaceImmersion B S hS W)))).obj K)
      (((smallEtaleDerivedPullbackData B S hS).pull
        (overProjection f (Over.mk (openSubspaceImmersion B S hS W)))).obj E) T₀ := by
  intro i hi
  let OW : Over Y := Over.mk (openSubspaceImmersion B S hS W)
  let T₁ : SchemesOver Y := (CostructuredArrow.map (S := schemeSpaceFunctor B S hS)
    (openSubspaceImmersion B S hS W)).obj T₀
  have hpb : IsPullback (baseChangeProjection (overInclusion f OW) T₀ ≫ overProjection f OW)
      (baseChangeInclusion (overInclusion f OW) T₀) f T₁.hom :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (overInclusion f OW) T₀.hom).paste_horiz
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f OW.hom)
  have hT₁ : IsPullback (baseChangeProjection f T₁) (baseChangeInclusion f T₁) f T₁.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T₁.hom
  rw [subsingleton_pull_comp_iff]
  exact (subsingleton_pull_iff_of_iso (hpb.isoIsPullback _ _ hT₁)
    (hpb.isoIsPullback_hom_fst _ _ hT₁) K E i).1 ((hW T₁ hT₀).1 (testPoint_map_mem W T₀) i hi)

/-- **Stacks 0DLC: part (2) reduces to the case `W = Y`.**  As in the source, part (2) is
formulated in terms of the algebraic spaces over `W` and the restrictions `X_W`, `K_W`, `E_W`: the
base change `X_W ⟶ W` is again proper, flat and of finite presentation, `K_W` is pseudo-coherent
(Stacks 08H4 for the representable morphism `X_W ⟶ X`), `E_W` is `W`-perfect (Stacks 0DKT at the
representable `X_W ⟶ X`,
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback`), the negative fibre
extensions of `K_W` and `E_W` vanish at every point of `W`
(`AlgebraicGeometry.Space.IsNegativeExtLocus.hasNoNegativeExtAt_restrict`), and for `V` over `W`
the base change `X_V` of `X` is the base change of `X_W`. -/
theorem NegativeExtVanishesOfFibres.negativeExtVanishesOverLocus
    (h : NegativeExtVanishesOfFibres B S hS) : NegativeExtVanishesOverLocus B S hS := by
  intro X Y f hp hflat hfp K E hK hE W hW V ⟨g, hg⟩ i hi
  let ι := openSubspaceImmersion B S hS W
  let OW : Over Y := Over.mk ι
  let fW := overInclusion f OW
  let pW := overProjection f OW
  have hsqW : IsPullback pW fW f ι := AlgebraicSpaces.isPullback_fiberProduct B S hS f OW.hom
  have hflatW : IsFlat B S hS fW.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hsqW hflat
  have hfpW : IsFinitePresentation B S hS fW.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsqW hfp
  have hrep : yoneda.relativelyRepresentable pW.hom :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hsqW).flip W.2.2.rep
  have hKW :
      (smallEtaleRingedSite B S hS (overBaseChange f OW).1 (overBaseChange f OW).2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull pW).obj K) :=
    isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS pW hrep K hK
  let V' : Over (openSubspaceAsSpace B S hS W) := Over.mk g
  have hpb : IsPullback (overProjection fW V' ≫ pW) (overInclusion fW V') f V.hom := by
    have hV' : IsPullback (overProjection fW V') (overInclusion fW V') fW g :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS fW V'.hom
    have := hV'.paste_horiz hsqW
    rwa [hg] at this
  have hV : IsPullback (overProjection f V) (overInclusion f V) f V.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom
  have key := h fW ((isProper_isStableUnderBaseChange B S hS).of_isPullback hsqW hp) hflatW hfpW
    _ _ hKW
    (isPerfectRelativeToCanonical_pull_of_isPullback hsqW hrep hflatW hfpW.1 hflat hfp.1 E hE)
    hW.hasNoNegativeExtAt_restrict V' i hi
  rw [subsingleton_pull_comp_iff] at key
  exact (subsingleton_pull_iff_of_iso (hpb.isoIsPullback _ _ hV)
    (hpb.isoIsPullback_hom_fst _ _ hV) K E i).2 key

end Reduction

end AlgebraicGeometry.Space

end
