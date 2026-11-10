module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAmbientDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalNonempty
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsite

/-!
# `hlev` on the affine objects alone: the affine objects determine a morphism of crystals

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean` leaves the faithfulness
half of [Stacks, Proposition 60.17.4, Tag 07JH] standing on one hypothesis that stands in for a
result the tree does not assemble: `hlev`, the weak finality of the levels, carried as a level
`level B` and a morphism `B ⟶ T_{level B}` for **every** object `B` of `Cris(X/S)`.

That hypothesis is stronger than the mathematics needs, and stronger than anything the tree can
supply.  A morphism `(U, T, δ) ⟶ (X, T_e, δ_e)` into a level is, `T_e` being affine over the base,
a divided power ring map out of the level into `Γ(T, 𝒪_T)`, and producing one means lifting the
generators of the polynomial presentation of `Γ(X, 𝒪_X)` through `Γ(T, 𝒪_T) ⟶ Γ(U, 𝒪_U)`.  For
affine `T` that lifting is free; for general `T` it is obstructed by the first cohomology of the
ideal sheaf, which is why `...exists_hom_to_specWholeSpaceThickening` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalNonempty.lean` carries
`[IsAffine B.thickening.source]` and why no statement in the tree produces such a morphism for a
non-affine object.  **`hlev` belongs on the affine objects**, and this module proves that there it
suffices — and then discharges the affine objects as well, leaving it on the thickenings of the
whole of `X`, where it is a statement about divided power rings.

## The reduction

Equality of two morphisms of sheaves of `𝒪_{X/S}`-modules is equality of their components at
every object of `Cris(X/S)`, and the affine objects generate a covering sieve of every object:
`...SmallSite.affineι_isCoverDense` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineSubsite.lean` proves that the
restrictions of an object to a cover of its ambient scheme by affine opens are affine objects and
cover it.  Only the *separatedness* half of the sheaf condition is used: a section of the target
sheaf is determined by its restrictions along the arrows out of the affine objects, so two
components agreeing at every affine object agree everywhere.

The separatedness statement is `CategoryTheory.Functor.IsCoverDense.ext`, which Mathlib provides
for sheaves of types.  The underlying additive presheaf of a sheaf of modules is a sheaf of
abelian groups, and the passage between the two is the corepresentability of the forgetful functor
of `AddCommGrpCat`, `AddCommGrpCat.uliftZMultiplesAddEquiv`; the forgetful functor itself is not
available, `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` asking that the target category's
morphisms live in the universe `max v₁ u₁` of the site, whereas the modules here live one universe
below.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `sheaf_ext_of_forall_affine_map_eq` — **separatedness of a sheaf of abelian groups on
  `Cris(X/S)` against the affine objects**: a section is determined by its restrictions along the
  morphisms out of the objects of `AffineCris(X/S)`.
* `eq_of_forall_affineObject_app_eq` — **two morphisms of sheaves of `𝒪_{X/S}`-modules which agree
  on the sections over every affine object are equal.**  No hypothesis on either sheaf beyond the
  sheaf condition they carry.
* `det_of_wholeSpaceLevelSections` — **`hdet` from the weak finality of the levels on the chaotic
  subsite `𝒞` alone**: two morphisms of crystals in quasi-coherent `𝒪_{X/S}`-modules agreeing on
  `Γ(T_e, ℱ)` for every level are equal, given a morphism to a level from every divided power
  thickening of the *whole* of `X`.
* `LevelComparison07JG.faithful_functor_of_wholeSpaceLevelSections` and
  `LevelReduction07JG.faithful_functor07JG_of_wholeSpaceLevelSections` — **the faithfulness half
  of [Stacks, Tag 07JH] with `hlev` asked only on the thickenings of the whole space.**

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no tag attribute is placed
in this module.**  The tag
asserts that the functor is an equivalence; only faithfulness is at issue here, and the full and
essentially-surjective halves are untouched.

What the faithfulness half costs after this module is

* `hlev` **on the chaotic subsite `𝒞`**: a level `level C` and a morphism
  `(wholeι S).obj C ⟶ T_{level C}` for every divided power thickening `C` of the whole of `X`,
  carried as data.  This is strictly weaker than the `hlev` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean` — the thickenings of
  the whole of an affine `X` are affine objects
  (`...SmallSite.isAffineObject_of_isOverWholeSpace`), so this quantifies over a subclass — and it
  is **no longer a statement about the site**: `...GlobalCrystallineSituation`'s
  `wholeSiteEquivLittleAffine` is an equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`, so it asks for a
  divided power ring map, which is the shape [Stacks, Lemma 60.5.6, Tag 07HP] has.
  `Crystalline.exists_levelThickening_hom` is that lemma for the finite levels of the completed
  envelope.  **`hlev` is proved**, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFamilyFinality.lean`, as
  `...SmallSite.exists_hom_to_wholeSpaceSystem_level`, and `hdet` with it, in
  `...SmallSite.det_of_wholeSpaceSystem`; that module also discharges `hlqc`.  `hlev` is a
  hypothesis here only because the identification of the two level families lives in
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFamilyIdentification.lean`, which this module
  does not import.  No `@[stacks 07JH]` attribute is placed there either: after `hdet` and `hlqc`
  the faithfulness half still rests on `hsurj`, which [Stacks, Tag 07JH] does not assume, and the
  full and essentially-surjective halves are nowhere proved.

  What stood between the two was the identification of the level family
  `Crystalline.exists_levelThickening_hom` names, `Crystalline.levelThickeningObj` of
  `Crystalline.completedCrystallineThickening`, with the levels
  `...SmallSite.wholeSpaceSystemLevel` of `...SmallSite.wholeSpaceSystem` that this hypothesis is
  stated over.  The two apparent obstructions to it **both dissolve** rather than being
  overcome.  The two families are envelopes of
  different presentation algebras even in degree zero —
  `Crystalline.tensorPowerPresentation s f 0` presents `s.C` from `MvPolynomial (Fin 1 × ι) s.A`
  while `Crystalline.completedCrystallineThickening s f hf` is over `MvPolynomial ι s.A` — but no
  comparison of the two presentations is needed, because `Crystalline.levelFamilyIso` is stated for
  an arbitrary presentation and an arbitrary object of `Cris^∧(C/A)` subject to three pinning
  hypotheses, so it applies at `Crystalline.tensorPowerPresentation s f 0` directly; and the three
  pinning hypotheses are then three fields of `Crystalline.CompletedEnvelopeThickening` on the
  nose, after the two `rfl`s `Crystalline.completedEnvelopeDPRing_eq` and
  `Crystalline.presentationEnvelope_eq_polynomialDividedPowerEnvelope`.
  `Crystalline.envelopeCodiagonal`, the morphism of *uncompleted* envelopes this note named as the
  only available comparison of the two presentations, is not used and is not needed.  The index
  offset — `...SmallSite.wholeSpaceSystemLevel` at `Crystalline.uniformLevel + e` against a bare
  `e` — costs nothing once the existence statement is in the `∀ e, N ≤ e` form rather than the
  `∃ e` form, which `Crystalline.exists_forall_le_levelEnvelope_hom` already supplies on the first
  family: a level past both cutoffs can then be *written* as `uniformLevel s + e`, so no lemma
  absorbing the offset is wanted;
* `hL`, that the system is the degree-zero member of `...SmallSite.wholeSpaceSystem`, a
  **delimiter and not a weakening** — it is the field
  `...SmallSite.Reduction07JG.levelSystem_isLevel` on the nose and is refuted by the degenerate
  system (`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`);
* `hlqc` and `hsurj`, the source's own standing hypotheses at [Stacks, Tag 07JN].

Two passages are **no longer** among them.  The passage from the affine objects to the whole site
was the step `StacksFrontier/AlgebraicGeometry/Crystalline/LevelAmbientDeterminacy.lean` paid for by
quantifying `hlev` over every object; it is proved here from cover-density of the affine subsite.
The passage from the thickenings of the whole space to the affine objects is
`...SmallSite.exists_hom_to_wholeSpaceThickening`, which is already proved and is used here
rather than assumed.  What is left of `hlev` is therefore entirely on the ring side, which is why
`LevelFamilyFinality.lean` can discharge it without touching the site again.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace SmallSite

/-! ### Separatedness of a sheaf of abelian groups against the affine objects -/

/-- The morphism of abelian groups out of `ULift ℤ` sending `ULift.up 1` to a prescribed element.
This is the corepresentation of the forgetful functor of `AddCommGrpCat`,
`AddCommGrpCat.uliftZMultiplesAddEquiv`, in the direction used below. -/
private noncomputable def intGen {M : AddCommGrpCat.{u}} (s : M) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶ M :=
  AddCommGrpCat.ofHom (uliftZMultiplesHom M s)

/-- `intGen s` sends `ULift.up 1` to `s`. -/
private theorem intGen_apply_one {M : AddCommGrpCat.{u}} (s : M) :
    intGen s (ULift.up (1 : ℤ)) = s := by
  change uliftZMultiplesHom (M : Type u) s (ULift.up (1 : ℤ)) = s
  rw [uliftZMultiplesHom_apply_apply]
  exact one_smul ℤ s

/-- An element is determined by the morphism `intGen` attaches to it. -/
private theorem intGen_injective {M : AddCommGrpCat.{u}} :
    Function.Injective (intGen (M := M)) := by
  intro s t h
  rw [← intGen_apply_one s, ← intGen_apply_one t, h]

/-- `intGen` is natural: postcomposing with a morphism of abelian groups is `intGen` of the
image. -/
private theorem intGen_comp {M N : AddCommGrpCat.{u}} (g : M ⟶ N) (s : M) :
    intGen s ≫ g = intGen (g s) := by
  ext n
  change g (uliftZMultiplesHom (M : Type u) s n) =
    uliftZMultiplesHom (N : Type u) (g s) n
  rw [uliftZMultiplesHom_apply_apply, uliftZMultiplesHom_apply_apply, map_zsmul]

/-- **Separatedness of a sheaf of abelian groups on `Cris(X/S)` against the affine objects.**  Two
sections over an object `B` which agree after restriction along every morphism into `B` out of an
object of `AffineCris(X/S)` are equal.

The affine objects generate a covering sieve of `B`, by `...SmallSite.affineι_isCoverDense`, so
this is the separatedness half of the sheaf condition for that sieve.  It is
`CategoryTheory.Functor.IsCoverDense.ext`, which is stated for sheaves of types, applied to the
sheaf of types `Hom(ℤ, -) ∘ N` of `CategoryTheory.Presheaf.IsSheaf`'s own definition; a section of
`N` over `B` is a morphism out of `ULift ℤ` by
`AddCommGrpCat.uliftZMultiplesAddEquiv`, which is where the two spellings meet. -/
theorem sheaf_ext_of_forall_affine_map_eq
    {N : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hN : Presheaf.IsSheaf (smallTopology S) N) {B : CrystallineThickening S}
    {s t : N.obj (op B)}
    (h : ∀ (A : AffineCrystallineThickening S) (f : (affineι S).obj A ⟶ B),
      N.map f.op s = N.map f.op t) :
    s = t := by
  have := affineι_isCoverDense S
  refine intGen_injective ?_
  refine Functor.IsCoverDense.ext (affineι S)
    ⟨N ⋙ coyoneda.obj (op (AddCommGrpCat.of (ULift.{u} ℤ))),
      (isSheaf_iff_isSheaf_of_type _ _).2 (hN _)⟩ B fun {A} f ↦ ?_
  change intGen s ≫ N.map f.op = intGen t ≫ N.map f.op
  rw [intGen_comp, intGen_comp, h A f]

/-- **Separatedness of a sheaf of `𝒪_{X/S}`-modules against the affine objects**, in the spelling
of `PresheafOfModules`: two sections over an object which agree after restriction along every
morphism out of an affine object are equal.

This is `...SmallSite.sheaf_ext_of_forall_affine_map_eq` at the underlying additive sheaf, whose
restriction maps are the restriction maps of the presheaf of modules on the nose
(`PresheafOfModules.presheaf_map_apply_coe`). -/
theorem section_ext_of_forall_affine_map_eq
    {F : SheafOfModules.{u} (structureSheaf S)} {B : CrystallineThickening S}
    {s t : (F.val : PresheafOfModules.{u} (crisRing S)).obj (op B)}
    (h : ∀ (A : AffineCrystallineThickening S) (f : (affineι S).obj A ⟶ B),
      (F.val : PresheafOfModules.{u} (crisRing S)).map f.op s =
        (F.val : PresheafOfModules.{u} (crisRing S)).map f.op t) :
    s = t :=
  sheaf_ext_of_forall_affine_map_eq F.isSheaf h

/-- **Two morphisms of sheaves of `𝒪_{X/S}`-modules which agree on the sections over every affine
object of `Cris(X/S)` are equal.**

Equality of the two morphisms is equality of their components at every object, and the component
at an arbitrary object is determined by the components at the affine objects: the target is a
sheaf, the affine objects cover every object by `...SmallSite.affineι_isCoverDense`, and
`...SmallSite.sheaf_ext_of_forall_affine_map_eq` is the separatedness that follows.  The
naturality squares of the two morphisms carry the agreement over the affine objects to the
restrictions of a section over the arbitrary one.

This carries no hypothesis on either sheaf beyond the sheaf condition in `SheafOfModules`. -/
theorem eq_of_forall_affineObject_app_eq
    {F G : SheafOfModules.{u} (structureSheaf S)} {psi chi : F ⟶ G}
    (h : ∀ B : CrystallineThickening S, IsAffineObject S B →
      ∀ x : (F.val : PresheafOfModules.{u} (crisRing S)).obj (op B),
        (PresheafOfModules.Hom.app psi.val (op B)).hom x =
          (PresheafOfModules.Hom.app chi.val (op B)).hom x) :
    psi = chi := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun X ↦ ?_)
  obtain ⟨B⟩ := X
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine section_ext_of_forall_affine_map_eq (F := G) fun A f ↦ ?_
  rw [← PresheafOfModules.naturality_apply psi.val f.op x,
    ← PresheafOfModules.naturality_apply chi.val f.op x]
  exact h A.obj A.property _

/-! ### `hdet` and faithfulness from the thickenings of the whole space -/

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {L : LevelScalars07JG S D}

/-- **`hdet` from the weak finality of the levels on the chaotic subsite `𝒞` alone.**  Two
morphisms of crystals in quasi-coherent `𝒪_{X/S}`-modules which agree on `Γ(T_e, ℱ)` for every
level `T_e` are equal, given a morphism to a level from every divided power thickening of the
*whole* of `X`.

The affine half of the weak finality is **discharged**, not carried:
`...SmallSite.exists_hom_to_wholeSpaceThickening` gives every affine object a morphism to an
object of `𝒞`, which is [Stacks, Lemma 60.5.6, Tag 07HP] translated across the affine-to-global
bridge, and `...SmallSite.eq_of_forall_affineObject_app_eq` carries the affine objects to the
whole site.  What is left is a morphism out of an object of `𝒞` into a level, and `𝒞` is where
[Stacks, Tag 07HP] itself lives: `...GlobalCrystallineSituation.wholeSiteEquivLittleAffine` is an
equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))`, so this hypothesis is a statement about divided power
rings and not about the site.

This is **not** [Stacks, Tag 07JH] — the tag is an equivalence statement — and no tag attribute is
placed. -/
theorem det_of_wholeSpaceLevelSections [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (level : WholeSpaceThickening S → ℕ)
    (hlev : ∀ C : WholeSpaceThickening S,
      (wholeι S).obj C ⟶ L.levelSystem.obj (level C))
    {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G)
    (hs : ∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
          (op (L.levelSystem.obj e))).hom s =
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
          (op (L.levelSystem.obj e))).hom s) :
    psi = chi := by
  classical
  refine (quasiCoherentCrystalι S).map_injective
    (eq_of_forall_affineObject_app_eq fun B hB x ↦ ?_)
  obtain ⟨C, ⟨f⟩⟩ := exists_hom_to_wholeSpaceThickening hp B hB
  rw [app_eq_of_moduleRestrictionSheafMap_eq B
    (moduleRestrictionSheafMap_eq_of_hom (isSheafCrystal_obj F) (f ≫ hlev C)
      (levelRestriction_of_isAffine hp hL hlqc psi chi hs (level C)))]

/-- **The faithfulness half of [Stacks, Tag 07JH] for the constructed functor, with `hlev` on the
chaotic subsite `𝒞` alone.**

`...SmallSite.LevelComparison07JG.faithful_functor_of_levelSections` runs on the weak finality of
the levels over every object of `Cris(X/S)`.  Here it is asked only over the divided power
thickenings of the whole of `X`: the passage from those to the affine objects is
`...SmallSite.exists_hom_to_wholeSpaceThickening` and the passage from the affine objects to the
whole site is `...SmallSite.eq_of_forall_affineObject_app_eq`.

`hL` is a **delimiter and not a weakening**: it is the field
`...SmallSite.Reduction07JG.levelSystem_isLevel` on the nose, and it is refuted by the degenerate
system over the empty open of `X`
(`...SmallSite.not_levelSystem_isLevel_preReduction07JGBot`).  `hlqc` and `hsurj` are the
source's own standing hypotheses at [Stacks, Tag 07JN].

No tag attribute is placed: [Stacks, Tag 07JH] asserts that the functor is an equivalence, and
only faithfulness is proved here. -/
theorem LevelComparison07JG.faithful_functor_of_wholeSpaceLevelSections [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (C : LevelComparison07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (level : WholeSpaceThickening S → ℕ)
    (hlev : ∀ C : WholeSpaceThickening S,
      (wholeι S).obj C ⟶ L.levelSystem.obj (level C)) :
    Functor.Faithful C.functor :=
  C.faithful_functor_of_isLevel hp hL hlqc hsurj
    fun psi chi hs ↦ det_of_wholeSpaceLevelSections hp hL hlqc level hlev psi chi hs

/-- **The faithfulness half of [Stacks, Tag 07JH] itself, with `hlev` on the chaotic subsite `𝒞`
alone.**  The passage from the constructed functor to the tag's own functor costs nothing, by
`...SmallSite.faithful_functor07JG_iff`.

No tag attribute is placed: the tag asserts that the functor is an equivalence, and the full and
essentially-surjective halves are untouched. -/
theorem LevelReduction07JG.faithful_functor07JG_of_wholeSpaceLevelSections [IsAffine S.X]
    [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hlqc : ∀ F : QuasiCoherentCrystal S, IsLocallyQuasiCoherent F.obj)
    (hsurj : ∀ F : QuasiCoherentCrystal S,
      CohomologyRestriction.IsSurjectiveComparison F.obj.val)
    (level : WholeSpaceThickening S → ℕ)
    (hlev : ∀ C : WholeSpaceThickening S,
      (wholeι S).obj C ⟶ L.levelSystem.obj (level C)) :
    Functor.Faithful (functor07JG (R.toReduction07JG (hp := hp) hL)) :=
  R.faithful_functor07JG_of_isLevel hp hL hlqc hsurj
    fun psi chi hs ↦ det_of_wholeSpaceLevelSections hp hL hlqc level hlev psi chi hs

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
