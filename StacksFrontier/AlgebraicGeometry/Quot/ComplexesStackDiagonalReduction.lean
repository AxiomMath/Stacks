module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageLeftEqualizer
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints
public import StacksFrontier.CategoryTheory.Sites.Stack.LocallyEssSurjOnFibersComp

/-!
# The diagonal of `Complexes_{X/B}` is representable (Stacks 0DLG)

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over `S`
(`AlgebraicGeometry.Space.ComplexesSituation`).  Stacks 0DLG says that the diagonal of the
category `Complexes_{X/Y}` of Stacks 0DLE over `(Sch/S)_{fppf}` is representable by algebraic
spaces.  This file proves it, granted parts (1) and (3) of Stacks 0DLC, which rest on Stacks 0DKY
and are carried as the hypotheses `AlgebraicGeometry.Space.ExistsNegativeExtLocus` and
`AlgebraicGeometry.Space.RelativeDerivedHomRepresentableOfFibres`.

The proof is the source's.  By Stacks 045G it suffices to show that for two objects `x`, `y` over
a scheme `U` the isomorphism sheaf `Isom(x, y)` is an algebraic space over `U`.

1. The isomorphism sheaf lives over the equalizer `Z₁ ⟶ U` of the two morphisms `U ⟶ Y`, a
   monomorphism of schemes; over `Z₁`, `x` and `y` restrict to two objects `x₁ = (Z₁, E₁)`,
   `y₁ = (Z₁, E₁')` over the same test scheme.
2. By Stacks 0DLC, part (1), there are opens `W`, `W'` of `Z₁` whose points with values in a field
   are those at which the negative extensions `Ext^{<0}(E₁, E₁')`, resp. `Ext^{<0}(E₁', E₁)`,
   vanish on the fibres.  An isomorphism `E₁ ≅ E₁'` on a fibre turns these into the negative
   self-extensions of `E₁` and `E₁'`, which vanish by condition (2) of Stacks 0DLD; so
   `Isom(x₁, y₁)` lives over the open subscheme `Z₂ = W ∩ W'`.
3. Over `Z₂` the negative extensions vanish on all fibres in both directions, and the last
   paragraph of the source
   (`AlgebraicGeometry.Space.ComplexesSituation.isULiftAlgebraic_isomPresheaf`, Stacks 08K9
   together with Stacks 0DLC, part (3)) shows that the isomorphism sheaf of the restrictions to
   `Z₂` is algebraic.
4. Replacing `Z₂` by `Z₁` and then `Z₁` by `U` along the two monomorphisms
   (`AlgebraicGeometry.Stack.exists_isAlgebraicOverSlice_isomPresheaf_of_mono`) concludes.

Nothing here is registered: the statement carries Stacks 0DLC, held pending Stacks 0DKY.

## Main results

* `AlgebraicGeometry.Space.IsOpenSubspace.mem_of_forall_isFieldObject`: an open subspace contains
  a section as soon as it contains its restrictions to the spectra of fields.
* `AlgebraicGeometry.Space.exists_mono_of_isOpenSubspace`: an open subspace of a scheme is an open
  subscheme.
* `AlgebraicGeometry.Space.ComplexesSituation.mem_of_relIso`: the support of the isomorphisms
  between the pullbacks of two complexes lies in the locus of part (1) of Stacks 0DLC.
* `AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal`: Stacks 0DLG,
  granted Stacks 0DLC, parts (1) and (3).

## References

* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Open subspaces and the spectra of fields -/

/-- **An open subspace is determined by its field-valued points.**  If the restriction of a section
`s` of `F` along every morphism `t : T₀ ⟶ V` from the spectrum of a field lies in an open subspace
`W`, then `s` lies in `W`: by Stacks 03BZ the open subspace `W` is the one cut out by its set of
points, and every point of `V` is represented by such a `t`. -/
theorem IsOpenSubspace.mem_of_forall_isFieldObject {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : Subfunctor F} (hW : IsOpenSubspace B S hS W) {V : BigFppfOver B S hS} (s : F.obj (op V))
    (h : ∀ T₀ : BigFppfOver B S hS, Stack.IsFieldObject B S hS T₀ → ∀ t : T₀ ⟶ V,
      F.map t.op s ∈ W.obj (op T₀)) :
    s ∈ W.obj (op V) := by
  have hle : openSubspaceOfPoints B S hS F (Set.range (pointsMap B S hS W.toFunctor W.ι)) ≤ W :=
    le_of_range_pointsMap_ι_subset B S hS hW
      (by rw [range_pointsMap_ι_openSubspaceOfPoints])
  refine hle (op V) ?_
  rw [mem_openSubspaceOfPoints_iff]
  rintro _ ⟨w, rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  have hp := h p.siteObject (Stack.isFieldObject_siteObject B S hS _ p)
    (p.value : p.siteObject ⟶ V)
  exact ⟨FieldValuedPoint.class B S hS W.toFunctor
    { carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase
      value := ⟨F.map (Quiver.Hom.op (p.value : p.siteObject ⟶ V)) s, hp⟩ }, rfl⟩

/-- **An open subspace of a scheme is an open subscheme**: for an open subspace `A` of the
algebraic space of a scheme `Z` of the site, there is a monomorphism `i : Z' ⟶ Z` of schemes of the
site through which a morphism `g : V ⟶ Z` factors if and only if `g` is a section of `A`. -/
theorem exists_mono_of_isOpenSubspace {Z : BigFppfOver B S hS} (A : Subfunctor (yoneda.obj Z))
    (hA : IsOpenSubspace B S hS A) :
    ∃ (Z' : BigFppfOver B S hS) (i : Z' ⟶ Z), Mono i ∧
      ∀ {V : BigFppfOver B S hS} (g : V ⟶ Z), (∃ k : V ⟶ Z', k ≫ i = g) ↔ g ∈ A.obj (op V) := by
  have := isRepresentable_of_isOpenSubspace_yoneda B S hS Z A hA
  let e := A.toFunctor.reprW
  let i : A.toFunctor.reprX ⟶ Z := yoneda.preimage (e.hom ≫ A.ι)
  have hi : yoneda.map i = e.hom ≫ A.ι := yoneda.map_preimage _
  have h1 : ∀ {V : BigFppfOver B S hS} (k : V ⟶ A.toFunctor.reprX),
      k ≫ i = (e.hom.app (op V) k).1 := fun k => congrArg (fun φ => φ.app (op _) k) hi
  refine ⟨_, i, ?_, fun {V} g => ⟨?_, fun hg => ?_⟩⟩
  · have : Mono (yoneda.map i) := by rw [hi]; infer_instance
    exact yoneda.mono_of_mono_map this
  · rintro ⟨k, rfl⟩
    rw [h1]
    exact (e.hom.app (op V) k).2
  · refine ⟨e.inv.app (op V) ⟨g, hg⟩, ?_⟩
    rw [h1]
    exact congrArg Subtype.val
      (e.inv_hom_id_app_apply (op V) (⟨g, hg⟩ : A.toFunctor.obj (op V)))

/-! ### Negative extensions at a point, along a cartesian square -/

/-- The negative extensions at a point `T₀ ⟶ Y` may be computed on any model of the fibre: for a
cartesian square `Z = X ×_Y T₀` with projection `p : Z ⟶ X`, they are the negative extensions
between the derived pullbacks along `p`. -/
theorem hasNoNegativeExtAt_iff_of_isPullback {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {T₀ : SchemesOver Y} {Z : AlgebraicSpaces B S hS} {p : Z ⟶ X}
    {q : Z ⟶ (schemeSpaceFunctor B S hS).obj T₀.left} (hpb : IsPullback p q f T₀.hom)
    (K E : derivedModules B S hS X) :
    HasNoNegativeExtAt f K E T₀ ↔ ∀ i : ℤ, i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull p).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull p).obj E)⟦i⟧) := by
  have hT : IsPullback (baseChangeProjection f T₀) (baseChangeInclusion f T₀) f T₀.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom
  exact forall₂_congr fun i _ => subsingleton_pull_iff_of_iso (hpb.isoIsPullback _ _ hT)
    (hpb.isoIsPullback_hom_fst _ _ hT) K E i

namespace ComplexesSituation

attribute [local instance] complexesCategory

variable {D : ComplexesSituation B S hS}

/-- **Negative extensions at a point, along a morphism of test schemes.**  For `h : T₂ ⟶ T₁` and a
point `T₀ ⟶ T₂`, the negative extensions of the derived pullbacks of `K` and `E` to `X_{T₂}` at
`T₀` are those of `K` and `E` at the point `T₀ ⟶ T₂ ⟶ T₁`: the two fibres are the same, by pasting
cartesian squares. -/
theorem hasNoNegativeExtAt_pull_relativeMap {T₂ T₁ : SchemesOver D.Y} (h : T₂ ⟶ T₁)
    (K E : derivedModules B S hS (D.space T₁))
    (T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T₂.left))
    (H : HasNoNegativeExtAt (D.projection T₁) K E
      (CostructuredArrow.mk (T₀.hom ≫ (schemeSpaceFunctor B S hS).map h.left))) :
    HasNoNegativeExtAt (D.projection T₂)
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj K)
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E) T₀ := by
  intro i hi
  have hT : IsPullback (baseChangeProjection (D.projection T₂) T₀)
      (baseChangeInclusion (D.projection T₂) T₀) (D.projection T₂) T₀.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T₂) T₀.hom
  have hpb := hT.paste_horiz (isPullback_baseChangeMap D.f h)
  rw [subsingleton_pull_comp_iff]
  exact (hasNoNegativeExtAt_iff_of_isPullback
    (T₀ := CostructuredArrow.mk (T₀.hom ≫ (schemeSpaceFunctor B S hS).map h.left)) hpb K E).1
    H i hi

/-- **Condition (2) of Stacks 0DLD at every point of the test scheme.**  For an object `E` of
`D(𝒪_{X_T})` satisfying condition (2) of Stacks 0DLD, the negative self-extensions of `E` vanish
at every point `T₀ ⟶ T` with values in a field, in the form of
`AlgebraicGeometry.Space.HasNoNegativeExtAt` for the projection `X_T ⟶ T`. -/
theorem hasNoNegativeExtAt_self {T : SchemesOver D.Y} {E : derivedModules B S hS (D.space T)}
    (hX : D.HasNoNegativeFibreExt T E)
    (T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left))
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) :
    HasNoNegativeExtAt (D.projection T) E E T₀ := by
  let g : T₀.left ⟶ T.left := yoneda.preimage T₀.hom.hom
  have hg : (schemeSpaceFunctor B S hS).map g = T₀.hom :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage T₀.hom.hom)
  have hpb := isPullback_baseChangeMap D.f (sliceTestHom D T (Over.mk g))
  change IsPullback _ _ _ ((schemeSpaceFunctor B S hS).map g) at hpb
  rw [hg] at hpb
  exact (hasNoNegativeExtAt_iff_of_isPullback hpb E E).2
    (fun i hi => hX ((sliceTest D T).obj (Over.mk g)) hT₀ (sliceTestHom D T (Over.mk g)) i hi)

/-- **The support of the isomorphisms lies in the locus of part (1) of Stacks 0DLC.**  Let `K`, `L`
be objects of `D(𝒪_{X_T})`, the negative self-extensions of `K` vanishing on the fibres
(condition (2) of Stacks 0DLD), and `W` a locus of part (1) of Stacks 0DLC for `Ext^{<0}(K, L)`.
If the pullbacks of `L` and `K` to `X_V` are isomorphic for `g : V ⟶ T`, then `g` factors through
`W`: on each fibre over a point of `V` with values in a field, `Ext^{<0}(K, L)` is
`Ext^{<0}(K, K) = 0`, so every such point lies in `W`. -/
theorem mem_of_relIso {T : SchemesOver D.Y} {K L : derivedModules B S hS (D.space T)}
    (hK : D.HasNoNegativeFibreExt T K)
    (W : OpenSubspaces B S hS ((schemeSpaceFunctor B S hS).obj T.left).1)
    (hW : IsNegativeExtLocus (D.projection T) K L W) (g : Over T.left)
    (α : ((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) L K).obj (op g)) :
    g.hom ∈ W.1.obj (op g.left) := by
  refine W.2.mem_of_forall_isFieldObject g.hom (fun T₀ hT₀ t => ?_)
  let g' : Over T.left := Over.mk (t ≫ g.hom)
  let α' := ((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
    (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) L K).map
      (Over.homMk t rfl : g' ⟶ g).op α
  have : IsIso α'.1 := α'.2
  have hsub : ∀ i : ℤ, i < 0 → Subsingleton
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (sliceTestHom D T g'))).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (sliceTestHom D T g'))).obj L)⟦i⟧) :=
    fun i hi => (subsingleton_hom_shift_congr (Iso.refl _) (asIso α'.1) i).2
      (hK ((sliceTest D T).obj g') hT₀ (sliceTestHom D T g') i hi)
  let T₁ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left) :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g'.hom)
  have hHas : HasNoNegativeExtAt (D.projection T) K L T₁ :=
    (hasNoNegativeExtAt_iff_of_isPullback (T₀ := T₁)
      (isPullback_baseChangeMap D.f (sliceTestHom D T g')) K L).2 hsub
  have hmem := (hW T₁ hT₀).2 hHas
  have e : testPoint T₁ = t ≫ g.hom := yonedaEquiv_yoneda_map _
  rwa [e] at hmem

/-! ### The restriction of an object along a morphism of test schemes -/

/-- The restriction of an object `(T', E)` of `Complexes_{X/Y}` along a morphism `h : T ⟶ T'` of
test schemes: the object `(T, L(X_h)^*E)` of Stacks 0DLF. -/
abbrev complexesRestrict (a : ComplexesObject D) {T : SchemesOver D.Y} (h : T ⟶ a.T) :
    ComplexesObject D where
  T := T
  E := ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj a.E
  relativelyPerfect := relativelyPerfectBaseChange D h a.E a.relativelyPerfect
  noNegativeFibreExt := D.hasNoNegativeFibreExt_pull h a.E a.noNegativeFibreExt

/-- The morphism from the restriction of `(T', E)` along `h` to `(T', E)`. -/
def complexesRestrictHom (a : ComplexesObject D) {T : SchemesOver D.Y} (h : T ⟶ a.T) :
    ComplexesHom (complexesRestrict a h) a where
  base := h
  fibre := 𝟙 _
  isIso_fibre := inferInstance

/-- `AlgebraicGeometry.Space.ComplexesSituation.complexesRestrict` as an object of the fibre. -/
abbrev complexesRestrictFiber (a : ComplexesObject D) {T : SchemesOver D.Y} (h : T ⟶ a.T) :
    (complexesFunctor D).Fiber T.left :=
  ⟨complexesRestrict a h, rfl⟩

/-- **The restriction is the pullback in the fibred category.**  If `x` lies over `U` and the
morphism `h : T ⟶ x.T` of test schemes is `j : T.left ⟶ U` up to the identification of `U` with
the underlying scheme of `x.T`, the restriction of `x` along `h` is isomorphic, in the fibre over
`T.left`, to the chosen pullback of `x` along `j`: every morphism of a category fibred in
groupoids is strongly cartesian. -/
def complexesRestrictFiberIso [(complexesFunctor D).IsFibered] {U : BigFppfOver B S hS}
    (x : (complexesFunctor D).Fiber U) {T : SchemesOver D.Y} (h : T ⟶ x.1.T) (j : T.left ⟶ U)
    (hh : h.left = j ≫ eqToHom x.2.symm) :
    complexesRestrictFiber x.1 h ≅
      (complexesFunctor D).pullbackFiber x j :=
  Functor.fiberIsoPullbackFiber (complexesFunctor D) x j _
    (complexesRestrictHom x.1 h : complexesRestrict x.1 h ⟶ x.1)
    (Functor.isStronglyCartesian_of_isFiberedInGroupoids (complexesFunctor_isFiberedInGroupoids D)
      j _ (IsHomLift.of_fac' (complexesFunctor D) j
        (complexesRestrictHom x.1 h : complexesRestrict x.1 h ⟶ x.1) rfl x.2
        (hh.trans (Category.id_comp _).symm)))

/-! ### Stacks 0DLG -/

/-- A functor to a universe-lifted type is its own lift by the identity of the larger universe. -/
def uliftIsoSelf {C : Type*} [Category* C] (F : C ⥤ Type (u + 1)) :
    F ≅ F ⋙ uliftFunctor.{u, u + 1} :=
  NatIso.ofComponents (fun _ => (Equiv.ulift.{u, u + 1}).toIso.symm) (fun _ => rfl)

variable (D) in
/-- **Stacks 0DLG, granted Stacks 0DLC, parts (1) and (3).**  The diagonal of `Complexes_{X/Y}` is
representable by algebraic spaces.

By Stacks 045G it suffices that the isomorphism sheaf of two objects `x`, `y` over a scheme `U` be
an algebraic space over `U`.  It lives over the equalizer `Z₁` of the two morphisms `U ⟶ Y`
(`AlgebraicGeometry.Space.ComplexesSituation.fiberBaseMap_eq_of_hom`), over which `x` and `y`
become two complexes `E₁`, `E₁'` on the same base change.  Part (1) of Stacks 0DLC gives the opens
`W`, `W'` of `Z₁` where `Ext^{<0}(E₁, E₁')`, resp. `Ext^{<0}(E₁', E₁)`, vanish on the fibres; the
isomorphism sheaf lives over `Z₂ = W ∩ W'`
(`AlgebraicGeometry.Space.ComplexesSituation.mem_of_relIso`), over which it is algebraic by the
last paragraph of the source
(`AlgebraicGeometry.Space.ComplexesSituation.isULiftAlgebraic_isomPresheaf`, which uses part (3)).
The two restrictions along the monomorphisms `Z₂ ⟶ Z₁ ⟶ U` do not change algebraicity
(`AlgebraicGeometry.Stack.exists_isAlgebraicOverSlice_isomPresheaf_of_mono`).

The two hypotheses are Stacks 0DLC, parts (1) and (3) (the latter in the case `W = Y`, to which
the source reduces it), which rest on Stacks 0DKY (not yet proved here). -/
theorem complexes_hasRepresentableDiagonal (h0DLC1 : ExistsNegativeExtLocus B S hS)
    (h0DLC3 : RelativeDerivedHomRepresentableOfFibres B S hS)
    (hp : (complexesFunctor D).IsFiberedInGroupoids) :
    Stack.HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk (complexesBasedCategory D) hp) := by
  let 𝒳 : CatFiberedInGroupoids (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory D) hp
  refine (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).2 ?_
  let : (complexesFunctor D).IsFibered := hp.isFibered
  intro U x y
  -- the equalizer `Z₁` of the two morphisms to the base
  obtain ⟨Z₁, j₁, hj₁, hZ₁⟩ := exists_mono_equalizer (D.fiberBaseMap x) (D.fiberBaseMap y)
  let T₁ : SchemesOver D.Y :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map j₁ ≫ D.fiberBaseMap x)
  have hxy : (schemeSpaceFunctor B S hS).map j₁ ≫ D.fiberBaseMap x =
      (schemeSpaceFunctor B S hS).map j₁ ≫ D.fiberBaseMap y :=
    (hZ₁ j₁).1 ⟨𝟙 _, Category.id_comp _⟩
  let hxT : T₁ ⟶ x.1.T := CostructuredArrow.homMk (j₁ ≫ eqToHom x.2.symm) (by
    rw [Functor.map_comp, Category.assoc]
    rfl)
  let hyT : T₁ ⟶ y.1.T := CostructuredArrow.homMk (j₁ ≫ eqToHom y.2.symm) (by
    rw [Functor.map_comp, Category.assoc]
    exact hxy.symm)
  let x₁ := complexesRestrictFiber x.1 hxT
  let y₁ := complexesRestrictFiber y.1 hyT
  let E := x₁.1.E
  let E' := y₁.1.E
  have hE : D.IsRelativelyPerfect T₁ E := x₁.1.relativelyPerfect
  have hE' : D.IsRelativelyPerfect T₁ E' := y₁.1.relativelyPerfect
  have hX : D.HasNoNegativeFibreExt T₁ E := x₁.1.noNegativeFibreExt
  have hX' : D.HasNoNegativeFibreExt T₁ E' := y₁.1.noNegativeFibreExt
  -- the loci of part (1) of Stacks 0DLC
  have hloc : ∀ K L : derivedModules B S hS (D.space T₁), D.IsRelativelyPerfect T₁ K →
      D.IsRelativelyPerfect T₁ L → ∃ W, IsNegativeExtLocus (D.projection T₁) K L W :=
    fun K L hK hL => h0DLC1 (D.projection T₁) (projection_isProper T₁) (D.projection_isFlat T₁)
      (projection_isFinitePresentation T₁) K L hK.1 hL
  obtain ⟨W, hW⟩ := hloc E E' hE hE'
  obtain ⟨W', hW'⟩ := hloc E' E hE' hE
  obtain ⟨Z₂, i, hi, hZ₂⟩ := exists_mono_of_isOpenSubspace (Z := T₁.left) (W.1 ⊓ W'.1)
    (isOpenSubspace_inf B S hS ((schemeSpaceFunctor B S hS).obj T₁.left).2 W.1 W'.1 W.2 W'.2)
  -- the restrictions to `Z₂`
  let x₂ := sliceTestFiber T₁ E hE hX (Over.mk i)
  let y₂ := sliceTestFiber T₁ E' hE' hX' (Over.mk i)
  have hmem : ∀ T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj Z₂),
      testPoint (CostructuredArrow.mk (T₀.hom ≫ (schemeSpaceFunctor B S hS).map i) :
        SchemesOver ((schemeSpaceFunctor B S hS).obj T₁.left)) ∈
          (W.1 ⊓ W'.1).obj (op T₀.left) :=
    fun T₀ => (hZ₂ _).1 ⟨yonedaEquiv T₀.hom.hom, (yonedaEquiv_comp T₀.hom.hom (yoneda.map i)).symm⟩
  have h₂ := isULiftAlgebraic_isomPresheaf ((sliceTest D T₁).obj (Over.mk i))
    (x₂.1.E) x₂.1.relativelyPerfect x₂.1.noNegativeFibreExt
    (y₂.1.E) y₂.1.relativelyPerfect y₂.1.noNegativeFibreExt h0DLC3
    (fun T₀ hT₀ => hasNoNegativeExtAt_pull_relativeMap (sliceTestHom D T₁ (Over.mk i)) E E' T₀
      ((hW _ hT₀).1 (hmem T₀).1))
    (fun T₀ hT₀ => hasNoNegativeExtAt_pull_relativeMap (sliceTestHom D T₁ (Over.mk i)) E' E T₀
      ((hW' _ hT₀).1 (hmem T₀).2))
    (fun T₀ hT₀ => hasNoNegativeExtAt_self x₂.1.noNegativeFibreExt T₀ hT₀)
    (fun T₀ hT₀ => hasNoNegativeExtAt_self y₂.1.noNegativeFibreExt T₀ hT₀)
  obtain ⟨G₂, hG₂, ⟨e₂⟩⟩ := h₂
  -- replacing `Z₂` by `Z₁`
  have hsupp₂ : ∀ g : Over T₁.left,
      Nonempty (((complexesFunctor D).isomPresheaf x₁ y₁).obj (op g)) →
        ∃ k : g.left ⟶ Z₂, k ≫ i = g.hom := by
    rintro g ⟨s⟩
    let α := (isomPresheafIsoRelIso T₁ E hE hX E' hE' hX').hom.app (op g) s
    have : IsIso α.1 := α.2
    exact (hZ₂ g.hom).2 ⟨mem_of_relIso hX W hW g α,
      mem_of_relIso hX' W' hW' g ⟨inv α.1, @IsIso.inv_isIso _ _ _ _ α.1 α.2⟩⟩
  obtain ⟨G₁, hG₁, ⟨e₁⟩⟩ := Stack.exists_isAlgebraicOverSlice_isomPresheaf_of_mono 𝒳 i x₁ y₁ x₂ y₂
    (complexesRestrictFiberIso x₁ (sliceTestHom D T₁ (Over.mk i)) i (Category.comp_id i).symm)
    (complexesRestrictFiberIso y₁ (sliceTestHom D T₁ (Over.mk i)) i (Category.comp_id i).symm)
    hsupp₂ G₂ hG₂ (e₂ ≪≫ uliftIsoSelf _)
  -- replacing `Z₁` by `U`
  have hsupp₁ : ∀ g : Over U, Nonempty (((complexesFunctor D).isomPresheaf x y).obj (op g)) →
      ∃ k : g.left ⟶ Z₁, k ≫ j₁ = g.hom := by
    rintro g ⟨s⟩
    exact (hZ₁ g.hom).2 (fiberBaseMap_eq_of_hom x y g.hom s.1)
  obtain ⟨G, hG, ⟨e⟩⟩ := Stack.exists_isAlgebraicOverSlice_isomPresheaf_of_mono 𝒳 j₁ x y x₁ y₁
    (complexesRestrictFiberIso x hxT j₁ rfl) (complexesRestrictFiberIso y hyT j₁ rfl)
    hsupp₁ G₁ hG₁ e₁
  exact Stack.isomPresheaf_algebraic_of_isAlgebraicOverSlice 𝒳 x y G hG e

end ComplexesSituation

end AlgebraicGeometry.Space

end
