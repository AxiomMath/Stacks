module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenGeneral
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.Topology.Sheaves.Modules.FiniteLocallyFreePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme

/-!
# The Picard functor of a pointed curve, and the locus where `Rf_{T,*}ℒ` is invertible

Let `k` be a field and let `f : X ⟶ Spec k` be a smooth projective curve with a `k`-rational point,
given as a section `σ` of `f`. The source (the running text of the chapter "Picard Schemes of
Curves" before [Stacks, Tag 0B9V]) considers the functor

`Pic_{X/k, σ} : (Sch/k)^{opp} ⟶ Ab, T ↦ Ker(Pic(X_T) ⟶ Pic(T))`,

the kernel of pullback along the section `σ_T : T ⟶ X_T` of `X_T = X ×_k T ⟶ T`.
[Stacks, Tag 0B9V] considers, for every `k`-scheme `T`, the subset `F(T) ⊆ Pic_{X/k, σ}(T)` of the
classes of invertible modules `ℒ` with `Rf_{T,*}ℒ` isomorphic to an invertible `𝒪_T`-module placed
in degree `0`, and asserts that `F` is a subfunctor and that the inclusion `F ⊆ Pic_{X/k, σ}` is
representable by open immersions. The source proof is: [Stacks, Tag 0B9S] with `i = 0`, `r = 1`.

## Main definitions

* `AlgebraicGeometry.RigidifiedPicard.picardFunctor`: **the functor `Pic_{X/k, σ}`**, on all
  schemes over `k` (`Over (Spec k)`), valued in abelian groups, built on the Picard group
  `Stacks.Picard.ofScheme` of [Stacks, Tag 01CX] and its pullback
  `Stacks.Picard.schemePullbackClassHom`.
* `AlgebraicGeometry.RigidifiedPicard.rankOneLocus`: the subsets `F(T)`.

## Main results

* `AlgebraicGeometry.RigidifiedPicard.rankOneLocus_isSubfunctor_and_representable`:
  **[Stacks, Tag 0B9V]**, untagged, with two named arguments: `hPerfBC`, the proposition of
  [Stacks, Tag 0A1H], and `hRankOpen`, description (2) of [Stacks, Tag 0BDK] for arbitrary
  morphisms. It carries no `@[stacks]` attribute while they are present.

## Implementation notes

**Representability by open immersions is stated pointwise**, which is its usual meaning: the
inclusion `F ⟶ Pic_{X/k, σ}` is representable by open immersions when for every `k`-scheme `T` and
every `ξ ∈ Pic_{X/k, σ}(T)` the fibre product `F ×_{Pic_{X/k, σ}} h_T` is represented by an open
subscheme `U ⊆ T`, i.e. there is an open `U ⊆ T` such that a morphism `g : T' ⟶ T` of `k`-schemes
satisfies `g^*ξ ∈ F(T')` exactly when `g` factors through `U`. That is the statement proved. It is
not stated through `CategoryTheory.MorphismProperty.presheaf`, which asks for presheaves valued in
the universe of the morphisms of `Over (Spec k)`, whereas Picard groups of schemes live one
universe higher.

**Invertible means finite locally free of rank one**, by clause 2 of [Stacks, Tag 0B8M]
(`Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one`); `F(T)` is
stated with `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, which is the form
[Stacks, Tag 0B9S] produces at `r = 1`.

## References

* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The section `σ_T : T ⟶ X_T` of `X_T = X ×_k T ⟶ T` induced by `σ`. -/
def sectionAt (T : Over (Spec (.of k))) : T.left ⟶ pullback f T.hom :=
  pullback.lift (T.hom ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- The transition morphism `X_{T'} ⟶ X_T` of a morphism `T' ⟶ T` of schemes over `k`. -/
def baseChangeMap {T T' : Over (Spec (.of k))} (g : T' ⟶ T) :
    pullback f T'.hom ⟶ pullback f T.hom :=
  pullback.map f T'.hom f T.hom (𝟙 X) g.left (𝟙 _) (by simp) (by simp)

/-- The transition morphism of the identity of `T` is the identity of `X_T`. -/
@[simp]
theorem baseChangeMap_id (T : Over (Spec (.of k))) : baseChangeMap f (𝟙 T) = 𝟙 _ := by
  ext <;> simp [baseChangeMap]

/-- The transition morphism of a composite `T'' ⟶ T' ⟶ T` is the composite of the transition
morphisms `X_{T''} ⟶ X_{T'} ⟶ X_T`. -/
theorem baseChangeMap_comp {T T' T'' : Over (Spec (.of k))} (g : T'' ⟶ T') (g' : T' ⟶ T) :
    baseChangeMap f (g ≫ g') = baseChangeMap f g ≫ baseChangeMap f g' := by
  apply pullback.hom_ext <;>
    simp only [baseChangeMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id, Over.comp_left]

/-- For a morphism `g : T' ⟶ T` over `k`, the sections are compatible: `σ_{T'}` followed by
`X_{T'} ⟶ X_T` equals `g` followed by `σ_T`. -/
theorem sectionAt_baseChangeMap {T T' : Over (Spec (.of k))} (g : T' ⟶ T) :
    sectionAt f σ hσ T' ≫ baseChangeMap f g = g.left ≫ sectionAt f σ hσ T := by
  apply pullback.hom_ext <;>
    simp only [sectionAt, baseChangeMap, pullback.map, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp, Over.w_assoc]


/-- The kernel `Ker(Pic(X_T) ⟶ Pic(T))` of pullback along the section `σ_T`. -/
abbrev kernelAt (T : Over (Spec (.of k))) :
    AddSubgroup (Stacks.Picard.ofScheme (pullback f T.hom)) :=
  (Stacks.Picard.schemePullbackClassHom (sectionAt f σ hσ T)).ker

/-- Pullback along `X_{T'} ⟶ X_T` maps the kernel at `T` into the kernel at `T'`, because the
sections are compatible (`sectionAt_baseChangeMap`). -/
def kernelMap {T T' : Over (Spec (.of k))} (g : T' ⟶ T) :
    kernelAt f σ hσ T →+ kernelAt f σ hσ T' :=
  AddMonoidHom.codRestrict
    ((Stacks.Picard.schemePullbackClassHom (baseChangeMap f g)).comp
      (kernelAt f σ hσ T).subtype) _ fun c => by
    change Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T')
      (Stacks.Picard.schemePullbackClass (baseChangeMap f g) c.1) = 0
    rw [Stacks.Picard.schemePullbackClass_comp, sectionAt_baseChangeMap,
      ← Stacks.Picard.schemePullbackClass_comp]
    have hc : Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) c.1 = 0 := c.2
    rw [hc]
    exact map_zero (Stacks.Picard.schemePullbackClassHom g.left)

/-- **The functor `Pic_{X/k, σ}`**: `T ↦ Ker(Pic(X_T) → Pic(T))`, the kernel of pullback along
the section `σ_T`. -/
def picardFunctor : (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (kernelAt f σ hσ T.unop)
  map g := AddCommGrpCat.ofHom (kernelMap f σ hσ g.unop)
  map_id T := by
    ext c
    change Stacks.Picard.schemePullbackClass (baseChangeMap f (𝟙 T.unop)) c.1 = c.1
    rw [baseChangeMap_id, Stacks.Picard.schemePullbackClass_id]
  map_comp {T T' T''} g g' := by
    ext c
    change Stacks.Picard.schemePullbackClass (baseChangeMap f (g'.unop ≫ g.unop)) c.1 =
      Stacks.Picard.schemePullbackClass (baseChangeMap f g'.unop)
        (Stacks.Picard.schemePullbackClass (baseChangeMap f g.unop) c.1)
    rw [baseChangeMap_comp, Stacks.Picard.schemePullbackClass_comp]

/-- **The subset `F(T) ⊆ Pic_{X/k, σ}(T)` of [Stacks, Tag 0B9V]**: the classes of invertible
`𝒪_{X_T}`-modules `ℒ` with `Rf_{T,*}ℒ` isomorphic to an invertible `𝒪_T`-module placed in degree
`0`. An invertible module on a scheme is a finite locally free module of rank `1`
(`Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one`), which is
how the condition is stated; the class is read through its chosen representative
`Stacks.Picard.picardRepresentative`, and the condition does not depend on the representative. -/
def rankOneLocus (T : Over (Spec (.of k))) : Set ((picardFunctor f σ hσ).obj (op T)) :=
  {c | ∃ M : T.left.Modules,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1 ∧
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule
          (pullback.snd f T.hom)
          (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace
            (c : kernelAt f σ hσ T).1).obj ≅
        (DerivedCategory.singleFunctor T.left.Modules 0).obj M)}

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
/-- **The open subscheme of `T` over which `ξ ∈ Pic_{X/k, σ}(T)` lies in `F`**: the open
subscheme of [Stacks, Tag 0B9S] for `f_T : X_T ⟶ T`, the chosen invertible representative `ℒ` of
`ξ`, `i = 0` and `r = 1` (`AlgebraicGeometry.ProperFlatRankOpen.rankOpen`). -/
def rankOneOpen (T : Over (Spec (.of k))) (c : (picardFunctor f σ hσ).obj (op T)) :
    T.left.Opens :=
  ProperFlatRankOpen.rankOpen (pullback.snd f T.hom)
    (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace
      (c : kernelAt f σ hσ T).1).obj 0 1

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
/-- **The inclusion `F ⊆ Pic_{X/k, σ}` is representable by open immersions**, with
[Stacks, Tag 0A1H] and [Stacks, Tag 0BDK] (2) as arguments: for `ξ ∈ Pic_{X/k, σ}(T)`,
represented by an invertible `ℒ` on `X_T`, the open subscheme of [Stacks, Tag 0B9S] for
`f_T : X_T ⟶ T`, `ℒ`,
`i = 0` and `r = 1` is `rankOneOpen T ξ`: `g^*ξ ∈ F(T')` exactly when `g` factors through it.
Only properness, flatness and local finite presentation of `f` are used. -/
theorem map_mem_rankOneLocus_iff
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (T : Over (Spec (.of k)))
    (c : (picardFunctor f σ hσ).obj (op T)) {T' : Over (Spec (.of k))} (g : T' ⟶ T) :
    (picardFunctor f σ hσ).map g.op c ∈ rankOneLocus f σ hσ T' ↔
      ∃ h : T'.left ⟶ (rankOneOpen f σ hσ T c).toScheme,
        h ≫ (rankOneOpen f σ hσ T c).ι = g.left := by
  let fT := pullback.snd f T.hom
  let L := (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace
    (c : kernelAt f σ hσ T).1)
  have hL1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (L.obj : (pullback f T.hom).Modules) 1 :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one _ _).1
      L.property
  have hLfp : (L.obj : (pullback f T.hom).Modules).IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFinitePresentation L.obj 1
  have : Flat fT := inferInstanceAs (Flat (pullback.snd f T.hom))
  have : IsProper fT := inferInstanceAs (IsProper (pullback.snd f T.hom))
  have : LocallyOfFinitePresentation fT :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f T.hom))
  have hfT : FinitePresentation fT := ⟨inferInstance, inferInstance, inferInstance⟩
  have hLflat : IsFlatOver fT.toLRSHom.toShHom (L.obj : (pullback f T.hom).Modules) :=
    @AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ _ fT _
      (L.obj : (pullback f T.hom).Modules)
      (@Stacks.Modules.isQuasicoherent_of_isFinitePresentation _ _ hLfp)
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        (L.obj : (pullback f T.hom).Modules) 1)
  have hsq : IsPullback (baseChangeMap f g) (pullback.snd f T'.hom) fT g.left := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback f T.hom)
    · have h1 : baseChangeMap f g ≫ pullback.fst f T.hom = pullback.fst f T'.hom := by
        simp only [baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]
      rw [h1, Over.w g]
      exact IsPullback.of_hasPullback f T'.hom
    · simp only [baseChangeMap, pullback.map, pullback.lift_snd, fT]
  change _ ↔ ∃ h : T'.left ⟶ (ProperFlatRankOpen.rankOpen fT L.obj 0 1).toScheme,
    h ≫ (ProperFlatRankOpen.rankOpen fT L.obj 0 1).ι = g.left
  rw [ProperFlatRankOpen.factorsThrough_rankOpen_iff_of_isPullback hPerfBC hRankOpen fT hfT
    inferInstance L.obj hLfp hLflat 0 1 g.left (pullback.snd f T'.hom) (baseChangeMap f g) hsq]
  let c' := (picardFunctor f σ hσ).map g.op c
  have hcl : Stacks.SheafOfModules.picardClass _ _
      (Stacks.Picard.picardRepresentative (pullback f T'.hom).toRingedSpace
        (c' : kernelAt f σ hσ T').1).obj
      (Stacks.Picard.picardRepresentative (pullback f T'.hom).toRingedSpace
        (c' : kernelAt f σ hσ T').1).property =
      Stacks.SheafOfModules.picardClass _ _
        ((Stacks.RingedSpace.pullbackFunctor (baseChangeMap f g).toLRSHom.toShHom).obj L.obj)
        (Stacks.RingedSpace.modulePullback_isInvertible_of _ _ L.property) :=
    Stacks.Picard.classOf_picardRepresentative _ _
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hcl
  let e' : (Stacks.Picard.picardRepresentative (pullback f T'.hom).toRingedSpace
        (c' : kernelAt f σ hσ T').1).obj ≅
      (Scheme.Modules.pullback (baseChangeMap f g)).obj L.obj := e
  let Φ := (DerivedCategory.singleFunctor _ 0) ⋙
    derivedPushforward (pullback.snd f T'.hom).toLRSHom.toShHom
  exact exists_congr fun M => and_congr_right fun _ =>
    ⟨fun ⟨w⟩ => ⟨Φ.mapIso e'.symm ≪≫ w⟩, fun ⟨w⟩ => ⟨Φ.mapIso e' ≪≫ w⟩⟩


open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
/-- The pointwise form of representability by open immersions: for `ξ ∈ Pic_{X/k, σ}(T)` there is
an open `U ⊆ T` such that `g^*ξ ∈ F(T')` exactly when `g` factors through `U`. -/
theorem exists_opens_map_mem_rankOneLocus_iff
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (T : Over (Spec (.of k)))
    (c : (picardFunctor f σ hσ).obj (op T)) :
    ∃ U : T.left.Opens, ∀ {T' : Over (Spec (.of k))} (g : T' ⟶ T),
      (picardFunctor f σ hσ).map g.op c ∈ rankOneLocus f σ hσ T' ↔
        ∃ h : T'.left ⟶ U.toScheme, h ≫ U.ι = g.left :=
  ⟨rankOneOpen f σ hσ T c, fun g => map_mem_rankOneLocus_iff f σ hσ hPerfBC hRankOpen T c g⟩

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward) in
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor) in
/-- **[Stacks, Tag 0B9V], with [Stacks, Tag 0A1H] (`hPerfBC`) and description (2) of [Stacks, Tag
0BDK] for arbitrary morphisms (`hRankOpen`) as arguments.** Let `k` be a field, let `X` be a smooth
projective curve over `k` and let `σ` be a `k`-rational point. For a scheme `T` over `k` consider
the subset `F(T) ⊆ Pic_{X/k, σ}(T)` of classes of invertible modules `ℒ` with `Rf_{T,*}ℒ`
isomorphic to an invertible `𝒪_T`-module placed in degree `0` (`rankOneLocus`). Then `F` is a
subfunctor of `Pic_{X/k, σ}` (first conjunct) and the inclusion is representable by open immersions
(second conjunct, stated pointwise as explained in the module documentation). -/
theorem rankOneLocus_isSubfunctor_and_representable
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    (hRankOpen : ∀ {Z : Scheme.{u}} (E : DerivedCategory Z.Modules),
      RingedSpace.IsPerfect (X := Z.toRingedSpace) E → ∀ (i : ℤ) (r : ℕ) {Y : Scheme.{u}}
        (h : Y ⟶ Z),
        (∃ g : Y ⟶ (Scheme.Modules.singleDegreeRankOpen E i r).toScheme,
            g ≫ (Scheme.Modules.singleDegreeRankOpen E i r).ι = h) ↔
          ∃ M : Y.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  h.toLRSHom.toShHom).obj E ≅
                (DerivedCategory.singleFunctor Y.Modules i).obj M))
    [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] :
    (∀ {T T' : Over (Spec (.of k))} (g : T' ⟶ T) (c : (picardFunctor f σ hσ).obj (op T)),
        c ∈ rankOneLocus f σ hσ T → (picardFunctor f σ hσ).map g.op c ∈ rankOneLocus f σ hσ T') ∧
      ∀ (T : Over (Spec (.of k))) (c : (picardFunctor f σ hσ).obj (op T)),
        ∃ U : T.left.Opens, ∀ {T' : Over (Spec (.of k))} (g : T' ⟶ T),
          (picardFunctor f σ hσ).map g.op c ∈ rankOneLocus f σ hσ T' ↔
            ∃ h : T'.left ⟶ U.toScheme, h ≫ U.ι = g.left := by
  have : IsProper f := inferInstance
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  have hrep := exists_opens_map_mem_rankOneLocus_iff f σ hσ hPerfBC hRankOpen
  refine ⟨fun {T T'} g c hc => ?_, hrep⟩
  obtain ⟨U, hU⟩ := hrep T c
  have hc' : (picardFunctor f σ hσ).map (𝟙 T).op c ∈ rankOneLocus f σ hσ T := by
    rw [op_id, CategoryTheory.Functor.map_id]
    exact hc
  obtain ⟨h, hh⟩ := (hU (𝟙 T)).1 hc'
  refine (hU g).2 ⟨g.left ≫ h, ?_⟩
  rw [Category.assoc, hh, Over.id_left, Category.comp_id]

end AlgebraicGeometry.RigidifiedPicard

end
