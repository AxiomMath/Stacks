module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor

/-!
# The splitting of the relative Picard sequence by a section (Stacks 0D28)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25, and let `σ : B ⟶ X` be a section of `f`.  For a test scheme `T`
over the base Stacks 0D27 writes down the sequence

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)`

whose first arrow is pullback along the projection `f_T : X_T ⟶ T` of the base change and whose
second is the component at `T` of the map from the presheaf of Picard groups to its fppf
sheafification.  Stacks 0D28 asserts that, when `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for
every `T`, the sequence is exact, is exact also on the right, and *splits*, a splitting being
pullback `σ_T^*` along the section `σ_T : T ⟶ X_T` of the base change.

This file proves the splitting and the exactness at `Pic(T)` that it forces.  Pullback of Picard
classes along `σ_T` retracts pullback along `f_T`, because `σ_T` is a section of `f_T` and
pullback of Picard classes along a composite is the composite of the pullbacks; retracting an
arrow makes it injective, which is exactness at `Pic(T)`, and makes `Pic(X_T)` the direct sum of
the image of `Pic(T)` and the kernel of `σ_T^*`, which is what a splitting of the sequence
amounts to.  The last statement needs pullback of Picard classes to be additive, that is the
inverse image of modules to be monoidal, which the development proves.

## Main definitions

* `AlgebraicGeometry.Space.ModulePullbackTensorIso`: the monoidality of the inverse image of
  Stacks 03LU at a tensor product of modules, the assertion `q^*(L ⊗ N) ≅ q^*L ⊗ q^*N`, in the
  spelling of the tensor product that adds Picard classes.
* `AlgebraicGeometry.Space.picardPullbackHom`: pullback of Picard classes along a morphism of
  algebraic spaces, as a homomorphism of Picard groups.
* `AlgebraicGeometry.Space.PicardSituation.basePicardPullbackHom` and
  `AlgebraicGeometry.Space.PicardSituation.sectionPicardPullbackHom`: **the first arrow
  `Pic(T) ⟶ Pic(X_T)` of the sequence of Stacks 0D28 and the splitting `σ_T^*`**, as
  homomorphisms of Picard groups.

## Main results

* `AlgebraicGeometry.Space.modulePullbackPicardTensorIso`: the inverse image of a tensor
  product of modules is the tensor product of the inverse images.
* `AlgebraicGeometry.Space.picardPullback_add` and
  `AlgebraicGeometry.Space.picardPullback_zero`: pullback of Picard classes is additive, and
  carries the trivial class to the trivial class.
* `AlgebraicGeometry.Space.PicardSituation.leftInverse_sectionPicardPullback`: **Stacks 0D28,
  the splitting** — `σ_T^*` retracts pullback along `f_T`.
* `AlgebraicGeometry.Space.PicardSituation.injective_basePicardPullback_of_section`:
  **Stacks 0D28, exactness at `Pic(T)`** — pullback along `f_T` is injective.  In the presence of
  a section this needs nothing about `𝒪_T ⟶ f_{T, *}𝒪_{X_T}`.
* `AlgebraicGeometry.Space.PicardSituation.existsUnique_add_sectionPicardPullback_eq_zero`:
  **Stacks 0D28, the direct sum decomposition the splitting gives** — every Picard class on `X_T`
  is uniquely the sum of a class pulled back from `T` and a class killed by `σ_T^*`.
* `AlgebraicGeometry.Space.PicardSituation.mem_range_basePicardPullback_iff`: a Picard class on
  `X_T` is pulled back from `T` exactly when it is recovered from its restriction along `σ_T`.

## Implementation notes

**What of Stacks 0D28 is here, and what is not.**  The conclusion of Stacks 0D28 has four parts:
exactness of the sequence at `Pic(T)`, at `Pic(X_T)` and at `Pic_{X/B}(T)`, and the splitting by
`σ_T^*`.  The splitting and the exactness at `Pic(T)` are proved here, together with the direct
sum decomposition of `Pic(X_T)` that the splitting produces.  The full statement of Stacks 0D28,
with all four parts and no hypothesis beyond the source's, is
`AlgebraicGeometry.Space.PicardSituation.picardSequence_splitExact` in
`StacksFrontier/AlgebraicGeometry/Quot/PicardSequenceSplitExact.lean`, where the coherence datum below
is the unconditional `AlgebraicGeometry.Space.modulePushforwardCoherence`.

The other two parts are **not** proved, and the obstruction is the one recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean`.  Exactness at
`Pic(X_T)` says that a Picard class dies in the sheafification exactly when it comes from `T`;
the inclusion that a class pulled back from `T` dies needs an invertible `𝒪_T`-module to be
trivial on an fppf covering family, which for the small étale site of a scheme of the site is not
available in this development (`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible`
is the statement for a ringed space whose stalks are local rings, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleBraidingSelf.lean` records that an
invertible module on a general site need not be locally trivial).  The reverse inclusion, and
exactness at `Pic_{X/B}(T)`, are the source's descent argument: that the presheaf `T ↦ ker σ_T^*`
is already an fppf sheaf, so that the sheafification does not change it.  That argument runs
through the units `u_{ij}` of the structure sheaf of `T` and the functions `f_{ijk}` on `X_T`
which the hypothesis on `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` identifies, and there is no sheaf of units and no
group of global units of the structure sheaf of an algebraic space in this development; the same
gap is what stops the two remaining halves of Stacks 0D2B in
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackSection.lean`.

**The hypothesis of Stacks 0D28 is not needed for what is proved.**  Stacks 0D28 assumes
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` to be an isomorphism for every `T`, which is
`AlgebraicGeometry.Space.PicardSituation.StructureSheafMapIso`.  Neither the splitting nor the
injectivity it forces uses it: a retraction of an arrow of abelian groups makes that arrow
injective whatever else is true.  In particular the exactness at `Pic(T)` proved here is a
strengthening of `AlgebraicGeometry.Space.PicardSituation.injective_basePicardPullback`, the same
conclusion obtained in Stacks 0D27 from that hypothesis together with the unit of the Stacks 03LU
adjunction being an isomorphism at an invertible module; in Situation 0D25 *with a section* both
of those inputs are dispensable.  The hypothesis is what the two unproved parts need.

**One hypothesis is carried, and it is the pseudofunctoriality of the direct images.**
`AlgebraicGeometry.Space.ModulePushforwardCoherence` is inherited unchanged from
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean` and from
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackSection.lean`; its unit law is what makes
pullback along an identity the identity and hence what turns `σ_T ≫ f_T = 𝟙_T` into a
retraction.

The two statements about the inverse image of modules that the splitting rests on are proved
and not assumed.  That the inverse image of an invertible module is invertible, without which
there is no map `Pic(X_T) → Pic(X_U)` at all, is
`AlgebraicGeometry.Space.modulePullbackInvertible`.  That the inverse image of a tensor product
is the tensor product of the inverse images is
`AlgebraicGeometry.Space.modulePullbackPicardTensorIso`, which reads
`AlgebraicGeometry.Space.modulePullbackTensorIso` at the spelling of the tensor product in which
addition of Picard classes is tensor product (`AlgebraicGeometry.Space.picardClass_add`); it is
what makes pullback of Picard classes a *homomorphism* of Picard groups, and therefore what lets
the retraction be read as a direct sum decomposition rather than only as a retraction of sets.

**Why the splitting is stated for the honest two arrows.**  The first arrow of the sequence is
`AlgebraicGeometry.Space.PicardSituation.basePicardPullback` and the splitting is
`AlgebraicGeometry.Space.PicardSituation.sectionPicardPullback`, both as they are defined for
Stacks 0D27 and 0D2B; the statements here are about those maps and not about reconstructed
copies of them, and the bundled homomorphisms of this file agree with them by definition.

**Why `Pic_{X/B}(T)` carries no group structure.**  The relative Picard functor of Stacks 0D25 is
built in this development as the fppf sheafification of a presheaf of *sets*; the additivity of
pullback is proved only here, downstream of it, so `T ↦ Pic(X_T)` is not presented there as a
presheaf of abelian groups.  The third term of the sequence is therefore a type with no zero,
and the two parts of Stacks 0D28 that mention it could only be stated as the equality of the
fibre of the second arrow over the image of the trivial class with the image of the first arrow,
and as surjectivity of the second arrow.  Neither is stated, because neither is proved.

## References

* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 0D2B](https://stacks.math.columbia.edu/tag/0D2B)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Additivity of the pullback of Picard classes -/

/-- **The monoidality of the inverse image of modules, in the spelling of the tensor product
that adds Picard classes.**  The assertion that the inverse image of a tensor product of
`𝒪_V`-modules along a morphism `q : W ⟶ V` of algebraic spaces is the tensor product of the
inverse images.

It is what makes pullback of Picard classes additive, and it is proved by
`AlgebraicGeometry.Space.modulePullbackPicardTensorIso`. -/
def ModulePullbackTensorIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (L N : Modules.{u, u} B S hS V.1 V.2),
    Nonempty ((modulePullback B S hS q).obj (picardTensorModule B S hS V.2 L N) ≅
      picardTensorModule B S hS W.2 ((modulePullback B S hS q).obj L)
        ((modulePullback B S hS q).obj N))

/-- **The inverse image of a tensor product of modules on an algebraic space is the tensor
product of the inverse images.**  This is
`AlgebraicGeometry.Space.modulePullbackTensorIso`, read at the spelling of the tensor product in
which addition of Picard classes is tensor product through
`AlgebraicGeometry.Space.modulesTensorObjIso` on each side. -/
theorem modulePullbackPicardTensorIso : ModulePullbackTensorIso B S hS := by
  intro V W q L N
  exact ⟨(modulePullback B S hS q).mapIso (modulesTensorObjIso B S hS V.1 V.2 L N).symm ≪≫
    modulePullbackTensorIso B S hS q L N ≪≫
    modulesTensorObjIso B S hS W.1 W.2 ((modulePullback B S hS q).obj L)
      ((modulePullback B S hS q).obj N)⟩

/-- **Pullback of Picard classes is additive.**  Addition in the Picard group is the tensor
product of invertible modules, so this is the monoidality of the inverse image read on
isomorphism classes. -/
theorem picardPullback_add {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (x y : picardGroup V) :
    picardPullback q (x + y) = picardPullback q x + picardPullback q y := by
  obtain ⟨Vo, hVo⟩ := V
  obtain ⟨Wo, hWo⟩ := W
  obtain ⟨L, hL, rfl⟩ := exists_picardClass _ x
  obtain ⟨N, hN, rfl⟩ := exists_picardClass _ y
  rw [picardClass_add B S hS hVo L N hL hN, picardPullback_picardClass,
    picardPullback_picardClass, picardPullback_picardClass,
    picardClass_add B S hS hWo _ _ (modulePullbackInvertible q L hL)
      (modulePullbackInvertible q N hN)]
  exact (picardClass_eq_picardClass_iff _ _ _ _ _).2 (modulePullbackPicardTensorIso q L N)

/-- **The pullback of Picard classes along a morphism of algebraic spaces, as a homomorphism of
Picard groups.** -/
def picardPullbackHom {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) :
    picardGroup V →+ picardGroup W :=
  AddMonoidHom.mk' (picardPullback q) (picardPullback_add q)

/-- The homomorphism `picardPullbackHom q` sends a Picard class `x` of `V` to
`picardPullback q x`. -/
@[simp]
theorem picardPullbackHom_apply {V W : AlgebraicSpaces B S hS} (q : W ⟶ V)
    (x : picardGroup V) : picardPullbackHom q x = picardPullback q x :=
  rfl

/-- **Pullback of Picard classes carries the trivial class to the trivial class.** -/
theorem picardPullback_zero {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) :
    picardPullback q 0 = 0 :=
  (picardPullbackHom q).map_zero

namespace PicardSituation

variable {s : PicardSituation B S hS}

/-! ### The first arrow of the sequence and its splitting -/

/-- **The first arrow `Pic(T) ⟶ Pic(X_T)` of the sequence of Stacks 0D28, as a homomorphism of
Picard groups**: pullback along the projection `f_T : X_T ⟶ T` of the base change. -/
def basePicardPullbackHom (T : s.SchemesOver) : s.basePicardAt T →+ s.picardAt T :=
  picardPullbackHom (baseChangeInclusion s.f T)

/-- The homomorphism `basePicardPullbackHom T` sends a class `x` of `Pic(T)` to its pullback
`s.basePicardPullback T x`. -/
@[simp]
theorem basePicardPullbackHom_apply (T : s.SchemesOver) (x : s.basePicardAt T) :
    basePicardPullbackHom T x = s.basePicardPullback T x :=
  rfl

/-- **The splitting `σ_T^* : Pic(X_T) ⟶ Pic(T)` of Stacks 0D28, as a homomorphism of Picard
groups**: pullback along the section `σ_T : T ⟶ X_T` of the base change. -/
def sectionPicardPullbackHom (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (T : s.SchemesOver) : s.picardAt T →+ s.basePicardAt T :=
  picardPullbackHom (baseChangeSection σ hσ T)

/-- The homomorphism `sectionPicardPullbackHom σ hσ T` sends a class `x` of `Pic(X_T)` to its
pullback `sectionPicardPullback σ hσ T x`. -/
@[simp]
theorem sectionPicardPullbackHom_apply (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (T : s.SchemesOver) (x : s.picardAt T) :
    sectionPicardPullbackHom σ hσ T x = sectionPicardPullback σ hσ T x :=
  rfl

/-- **Stacks 0D28, the splitting.**  Pullback of Picard classes along the section
`σ_T : T ⟶ X_T` of the base change retracts pullback along the projection `f_T : X_T ⟶ T`:
`σ_T^* ∘ f_T^*` is the identity of `Pic(T)`.  This is the splitting of the sequence

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T) ⟶ 0`

of Stacks 0D28, and it holds with no hypothesis on `𝒪_T ⟶ f_{T, *}𝒪_{X_T}`. -/
@[stacks 0D28 "auxiliary: the splitting by σ_T^* for an arbitrary 03LU coherence datum; the full statement, \
with no hypothesis, is picardSequence_splitExact"]
theorem leftInverse_sectionPicardPullback (hc : ModulePushforwardCoherence B S hS)
    (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver) :
    Function.LeftInverse (sectionPicardPullback σ hσ T) (s.basePicardPullback T) :=
  sectionPicardPullback_basePicardPullback hc σ hσ T

/-- **Stacks 0D28, exactness at `Pic(T)`.**  In Situation 0D25 with a section `σ : B ⟶ X` of `f`,
pullback along the projection `f_T : X_T ⟶ T` of the base change is an injection
`Pic(T) ⟶ Pic(X_T)`: it is retracted by `σ_T^*`.

Stacks 0D27 obtains the same conclusion from `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` being an isomorphism; with a
section neither that hypothesis nor the unit of the Stacks 03LU adjunction being an isomorphism at
an invertible module is needed. -/
@[stacks 0D28 "auxiliary: exactness at Pic(T) for an arbitrary 03LU coherence datum; the full statement, \
with no hypothesis, is picardSequence_splitExact"]
theorem injective_basePicardPullback_of_section (hc : ModulePushforwardCoherence B S hS)
    (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver) :
    Function.Injective (s.basePicardPullback T) :=
  (leftInverse_sectionPicardPullback hc σ hσ T).injective

/-! ### The direct sum decomposition the splitting gives -/

/-- **A Picard class on `X_T` is pulled back from `T` exactly when it is recovered from its
restriction along the section.** -/
theorem mem_range_basePicardPullback_iff (hc : ModulePushforwardCoherence B S hS)
    (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver) (x : s.picardAt T) :
    x ∈ Set.range (s.basePicardPullback T) ↔
      s.basePicardPullback T (sectionPicardPullback σ hσ T x) = x := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  rintro ⟨y, rfl⟩
  rw [leftInverse_sectionPicardPullback hc σ hσ T y]

/-- **Stacks 0D28, the direct sum decomposition.**  The splitting makes `Pic(X_T)` the direct sum
of the image of `Pic(T)` under `f_T^*` and the kernel of `σ_T^*`: every Picard class on `X_T` is
the sum of the pullback of a unique Picard class on `T` and a unique class killed by `σ_T^*`.

This is what "the sequence of Stacks 0D28 is split" says internally to `Pic(X_T)`; the
identification of the kernel of `σ_T^*` with `Pic_{X/B}(T)`, which is the remaining content of
Stacks 0D28, is not proved here. -/
@[stacks 0D28 "auxiliary: the direct sum decomposition for an arbitrary 03LU coherence datum; the full \
statement, with no hypothesis, is picardSequence_splitExact"]
theorem existsUnique_add_sectionPicardPullback_eq_zero (hc : ModulePushforwardCoherence B S hS)
    (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver) (x : s.picardAt T) :
    ∃! p : s.basePicardAt T × s.picardAt T,
      sectionPicardPullback σ hσ T p.2 = 0 ∧
        x = s.basePicardPullback T p.1 + p.2 := by
  have hrf : ∀ y, sectionPicardPullback σ hσ T (s.basePicardPullback T y) = y :=
    leftInverse_sectionPicardPullback hc σ hσ T
  refine ⟨⟨sectionPicardPullback σ hσ T x,
    x - s.basePicardPullback T (sectionPicardPullback σ hσ T x)⟩, ⟨?_, ?_⟩, ?_⟩
  · simpa [hrf] using map_sub (sectionPicardPullbackHom σ hσ T) x
      (s.basePicardPullback T (sectionPicardPullback σ hσ T x))
  · exact (add_sub_cancel _ _).symm
  · rintro ⟨y, k⟩ ⟨hk, hx⟩
    have hy : sectionPicardPullback σ hσ T x = y := by
      simpa [hx, hrf, hk] using map_add (sectionPicardPullbackHom σ hσ T)
        (s.basePicardPullback T y) k
    refine Prod.ext hy.symm ?_
    rw [hy, hx]
    exact (add_sub_cancel_left _ _).symm

end PicardSituation

end AlgebraicGeometry.Space

end
