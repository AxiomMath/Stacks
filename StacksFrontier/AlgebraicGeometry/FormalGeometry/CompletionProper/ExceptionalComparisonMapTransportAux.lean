module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Algebra.Module.IPowerTorsion.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.RingTheory.Rig.FlatBaseChangeReduction
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapBaseChangeAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapCompleteAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapFormalAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapSystemAux
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalChart

/-!
# Transport of the datum of Stacks 088B along a base change

Let `Y` be a Noetherian scheme, `𝒥, 𝒦 ⊆ 𝒪_Y` quasi-coherent sheaves of ideals and `f : X ⟶ Y`
a proper morphism which is an isomorphism over `Y ∖ V(𝒦)`. The source's proof of
[Stacks, Tag 088B] reduces the kernel–cokernel bound to the case of a base which is the spectrum
of a Noetherian ring complete along `𝒥`, by base changing the whole datum along the flat
morphism `Spec Γ(Y, U)^ ⟶ Y` attached to an affine open `U ⊆ Y`.

This file carries out the part of that reduction which concerns the comparison maps, in the
generality of an arbitrary commuting square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

rather than only for the completion chart: the comparison
`Stacks.Coherent.pushforwardCompletionComparison` from the completion of a direct image to the
direct image of a completion is carried by the base-change comparisons into the same comparison
for `f'`. That identity is the first of the two squares the transport of the defining equation
of `α` needs, and it is also what identifies the restriction of the comparison map to an affine
open, which is why it is stated for a general `g`.

Alongside it the file records the three facts about the geometric datum which survive a base
change — properness is a Mathlib instance, flatness of `g'` likewise, and invertibility of
`f ∣_ (Y ∖ V(𝒦))` is the content of
`Stacks.Coherent.isIso_morphismRestrict_pullback_snd` — the degree-zero flat base-change
isomorphism `g^*(f_*𝓕) ≅ f'_*((g')^*𝓕)` as an isomorphism, and the base change of the
isomorphism `β` of the source along the canonical square.

## Main definitions

* `Stacks.Coherent.pushforwardBaseChangeIso` — the degree-zero flat base-change comparison
  `g^*(f_*𝓕) ≅ f'_*((g')^*𝓕)`, as an isomorphism.
* `Stacks.Coherent.pushforwardCompletionBaseChange` — **the base-change comparison for the
  completion of a direct image**, from `g^*((f_*𝓕)^)` to `(f'_*((g')^*𝓕))^`.
* `Stacks.Coherent.pushforwardCompletionBaseChangeIso` — the same for the canonical square of a
  flat `g`, as an isomorphism of coherent adic systems.
* `Stacks.Coherent.completionSystemCongr` — the underlying inverse system of a completion,
  transported along an equality of ideal sheaves.
* `Stacks.Coherent.baseChangeDatumIso` — **the isomorphism `β` of Stacks 088B, transported
  along `g`**, together with `Stacks.Coherent.baseChangeDatumSystemIso`, its underlying natural
  isomorphism with the ideal sheaf of the corner left as a parameter.

## Main results

* `Stacks.Coherent.isIso_morphismRestrict_pullback_snd` — **the hypothesis of Stacks 088B is
  stable under base change.**
* `Stacks.Coherent.comap_comap_of_comm` — the two ways around a commuting square give the same
  inverse-image ideal sheaf.
* `Stacks.Coherent.completionProjection_pullbackCompletionTerm` — the levelwise comparison
  `(g')^*(𝓕^) ⟶ (((g')^*𝓕)^)` is normalised by the projections.
* `Stacks.Coherent.pushforwardCompletionBaseChange_comp_comparison` — **the base-change
  comparison intertwines the two comparison maps of a completed direct image** (the first of the
  two squares the transport of the defining equation of `α` needs).
* `Stacks.Coherent.directImageComparison_baseChange` — **the base-change comparison carries the
  maps `γ` of Stacks 088B to the maps `γ` of the transported datum** (the second square).
* `Stacks.Coherent.systemMap_baseChange_comp_comparison` — **the defining equation of the
  comparison map `α` of Stacks 088B survives the transport**, which is what lets the complete
  affine case be applied to the transported datum.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_eq_baseIdealSheafOnSpec` — the
  kernel–cokernel bound over a complete affine base, with the base ideal sheaf presented as a
  parameter, which is the form the completion chart supplies it in.
* `Stacks.Coherent.idealPowerMultiple_pullback_eq_bot_of_comp_iso` — **the annihilation of the
  levelwise kernels and cokernels of a flat inverse image reflects to the inverse images of the
  kernels and cokernels.**
* `Stacks.Coherent.comap_adicCompletionChart` — **the inverse image of `𝒥` along the completion
  chart of an affine open `U` is the ideal sheaf attached to the extension of `𝒥(U)` to the
  completion of `Γ(Y, U)`**, which is the ideal sheaf the complete affine case is indexed by.
* `Stacks.Coherent.appLE_adicCompletionChart` — **the completion chart induces the completion map
  `Γ(Y, U) ⟶ Γ(Y, U)^` on sections**, read through `AlgebraicGeometry.Scheme.ΓSpecIso`.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_isNoetherian` — **the kernel–cokernel
  bound of Stacks 088B over an arbitrary Noetherian base.**

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so a composite
whose factors are presented at the two spellings is accepted while no rewrite by
`CategoryTheory.Category.assoc` applies to it; every reassociation below is therefore performed
by the two private lemmas `comp_left` and `comp_right`, stated in an abstract category, as
`Stacks.Coherent.map_comp_eqToHom_comparison` is in the sibling file
`ExceptionalComparisonMapPullbackAux.lean` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/`.

The identification of the two inverse-image ideal sheaves of the corner is a *parameter* `hJ` of
the comparison and of the square, rather than `Stacks.Coherent.comap_comap_of_comm` applied
inside them, and the transport it induces is written out as an `eqToHom` rather than wrapped in a
definition. Both choices are forced by the kernel: a transport whose equality proof is a concrete
application of `comap_comap_of_comm`, or which has to be reached by unfolding a definition, makes
the kernel try to reduce `Eq.rec` through the ideal-sheaf machinery and the check does not
terminate. The normalisation
`Stacks.Coherent.completionProjection_pullbackCompletionTerm` is proved by generalising the
target ideal sheaf to a variable, substituting the equality away, and only then instantiating,
for the same reason.

The comparison is read through `Stacks.Coherent.pullbackCompletionComparison` rather than
through the components of `Stacks.Coherent.pullbackCompletionIso`: the latter presents its source
as a term of `Stacks.Coherent.coherentAdicPullback`, and the identification of that presentation
with the plain inverse image is another defeq the kernel does not survive.

The descent of the annihilation from the chart back to the base runs
`Stacks.Coherent.smul_eq_zero_of_injective_sectionsComparison` over the single pair of affine
opens `(U, ⊤)` — over `Y` rather than over `U.toScheme`, so that the two rings are exactly
`Γ(Y, U)` and `Γ(Spec Γ(Y, U)^, ⊤)` and no localization over a basic open intervenes. Its
semilinearity input is `AlgebraicGeometry.pullbackSectionHom_smul`, with the scalar map identified
by `Stacks.Coherent.appLE_adicCompletionChart`; triviality of the kernel of
`AlgebraicGeometry.Scheme.Modules.pullbackSection` is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` together with
`tensorProduct_mk_bijective_of_ideal_power_torsion`, whose torsion hypothesis is
`Stacks.Algebraization.isIPowerTorsion_sections_of_isPowerAnnihilated` and whose quotient-map
hypothesis is `Rig.bijective_quotientMap_pow_algebraMap_adicCompletion` transported along
`Scheme.ΓSpecIso` by `Rig.bijective_quotientMap_pow_of_ringEquiv`. The two tensor products are
matched by `IPowerTorsion.one_tmul_bijective`, which exchanges the two tensor orders, and by
`IPowerTorsion.tensorModuleCatEquiv`, which identifies `S ⊗[R] M` with
`ModuleCat.extendScalars`. Globalization is
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_restrict`, whose per-open input asks for
annihilation of the *restriction* to `U`; that is read off the sections over the whole of `U` by
`Stacks.Coherent.affine_idealPowerMultiple_eq_bot` on the affine scheme `U.toScheme`, which
presents those sections as the sections over `U.ι ''ᵁ ⊤` and so forces the hypothesis to be
generalised over the affine opens equal to `U` before the equality is substituted away.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Base change of the geometric datum -/

/-- The complement of the support of an inverse-image ideal sheaf is the inverse image of the
complement of the support. -/
public lemma support_comap_compl {Y Y' : Scheme.{u}} (K : Y.IdealSheafData) (g : Y' ⟶ Y) :
    (K.comap g).support.compl = g ⁻¹ᵁ K.support.compl := by
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  simp

/-- **The hypothesis of Stacks 088B is stable under base change.** If `f` restricts to an
isomorphism over the complement of the support of `𝒦`, then its base change along `g` restricts
to an isomorphism over the complement of the support of `𝒦.comap g`. -/
public lemma isIso_morphismRestrict_pullback_snd {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (K : Y.IdealSheafData) (hf : IsIso (f ∣_ K.support.compl)) :
    IsIso (Limits.pullback.snd f g ∣_ (K.comap g).support.compl) := by
  rw [support_comap_compl]
  set V := K.support.compl with hV
  have s := (isPullback_morphismRestrict (Limits.pullback.snd f g) (g ⁻¹ᵁ V)).paste_vert
    (IsPullback.of_hasPullback f g).flip
  rw [← morphismRestrict_ι g V] at s
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
    (IsPullback.of_bot' s (isPullback_morphismRestrict f V)).flip hf

/-- A scheme proper over a Noetherian scheme is Noetherian. -/
public lemma isNoetherian_of_isProper {A B : Scheme.{u}} (h : A ⟶ B) [IsNoetherian B]
    [IsProper h] : IsNoetherian A where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian h
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace h

/-! ### The degree-zero flat base-change isomorphism -/

section Zero

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Flat base change in degree zero, as an isomorphism** `g^*(f_*𝓕) ≅ f'_*((g')^*𝓕)` for the
canonical base-change square of `f` along a flat `g`. -/
public def pushforwardBaseChangeIso [Flat g] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ≅
      (Scheme.Modules.pushforward (Limits.pullback.snd f g)).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F) :=
  haveI : IsIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange
      (Limits.pullback.condition (f := f) (g := g)) F) := by
    rw [← Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
    exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      (IsPullback.of_hasPullback f g) F
  asIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange
    (Limits.pullback.condition (f := f) (g := g)) F)

/-- The isomorphism of `Stacks.Coherent.pushforwardBaseChangeIso` is the canonical comparison. -/
public lemma pushforwardBaseChangeIso_hom [Flat g] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    (pushforwardBaseChangeIso f g F).hom =
      Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange
        (Limits.pullback.condition (f := f) (g := g)) F :=
  rfl

end Zero

/-! ### The transported datum -/

/-- The direct image of a coherent module along a proper morphism, as a coherent module. -/
public abbrev pushforwardCoherentModule {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [IsProper f] (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  haveI := F.property
  ⟨(Scheme.Modules.pushforward f).obj F.obj,
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F.obj⟩

/-- **The two ways around a commuting square give the same inverse-image ideal sheaf.** -/
public lemma comap_comap_of_comm {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) (J : Y.IdealSheafData) :
    (J.comap f).comap g' = (J.comap g).comap f' := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, w]

section Transport

variable {X Y Y' : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
  (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [Flat g]
  [IsNoetherian (Limits.pullback f g)] (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The comparison of the base change of the completion of a direct image with the completion
of the direct image of the base change.** -/
public def pushforwardCompletionBaseChangeIso :
    (coherentAdicPullback g J).obj
        ((Stacks.Algebraization.completionFunctor Y J).obj
          (pushforwardCoherentModule f F)) ≅
      (Stacks.Algebraization.completionFunctor Y' (J.comap g)).obj
        (pushforwardCoherentModule (Limits.pullback.snd f g)
          (pullbackCoherentModule (Limits.pullback.fst f g) F)) :=
  haveI := F.property
  haveI : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  pullbackCompletionIso g J (pushforwardCoherentModule f F) ≪≫
    (Stacks.Algebraization.completionFunctor Y' (J.comap g)).mapIso
      (ObjectProperty.isoMk _ (pushforwardBaseChangeIso f g F.obj))

end Transport

/-- The underlying inverse system of a completion, transported along an equality of ideal
sheaves. Its components are the transports of the individual terms, so that nothing has to be
reduced through a natural transformation built by `CategoryTheory.eqToIso`. -/
public def completionSystemCongr {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    {L L' : Z.IdealSheafData} (h : L = L')
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    ((Stacks.Algebraization.completionFunctor Z L).obj M).obj ≅
      ((Stacks.Algebraization.completionFunctor Z L').obj M).obj :=
  NatIso.ofComponents
    (fun n => eqToIso (congrArg
      (fun T => ((Stacks.Algebraization.completionFunctor Z T).obj M).obj.obj n) h))
    (by subst h; intro i j a; simp)

/-- The components of `Stacks.Coherent.completionSystemCongr`. -/
public lemma completionSystemCongr_hom_app {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    {L L' : Z.IdealSheafData} (h : L = L')
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕᵒᵖ) :
    (completionSystemCongr h M).hom.app n =
      eqToHom (congrArg
        (fun T => ((Stacks.Algebraization.completionFunctor Z T).obj M).obj.obj n) h) :=
  rfl

/-- Reassociation on the left, in an abstract category: the automation for `≫` is obstructed by
the two descriptions of the category of `𝒪_X`-modules, so every reassociation of the diagram
chase below is performed here instead. -/
private lemma comp_left {C : Type*} [Category* C] {A B D E : C} {a : A ⟶ B} {b : B ⟶ D}
    {c : D ⟶ E} {z : A ⟶ D} (h : a ≫ b = z) : a ≫ b ≫ c = z ≫ c := by
  rw [← Category.assoc, h]

/-- Reassociation on the right, in an abstract category. -/
private lemma comp_right {C : Type*} [Category* C] {A B D E : C} {a : A ⟶ B} {b : B ⟶ D}
    {c : D ⟶ E} {z : B ⟶ E} (h : b ≫ c = z) : (a ≫ b) ≫ c = a ≫ z := by
  rw [Category.assoc, h]

/-- A functor carries a composite identity to the composite of the images, in an abstract
category. -/
private lemma map_comp_of_comp_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B Z : C} {a : A ⟶ B} {b : B ⟶ Z} {c : A ⟶ Z} (h : a ≫ b = c) :
    F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp, h]

/-- Cancellation of an isomorphism carried through a functor, in an abstract category. -/
private lemma map_hom_comp_map_inv_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B : C} (i : A ≅ B) {Z : D} (c : F.obj A ⟶ Z) :
    F.map i.hom ≫ F.map i.inv ≫ c = c := by
  rw [← Category.assoc, ← F.map_comp, i.hom_inv_id, F.map_id, Category.id_comp]

/-- Reassociation of a four-fold composite whose last two factors collapse, in an abstract
category. -/
private lemma comp_comp_cancel {C : Type*} [Category* C] {A B D E Z : C} (a : A ⟶ B) (b : B ⟶ D)
    {i : D ⟶ E} {c : E ⟶ Z} {c' : D ⟶ Z} (h : i ≫ c = c') :
    (a ≫ b ≫ i) ≫ c = a ≫ b ≫ c' := by
  rw [Category.assoc, Category.assoc, h]

/-- Reassociation past a transport along a reflexive equality, in an abstract category. -/
private lemma comp_comp_eqToHom_refl {C : Type*} [Category* C] {A B D : C} {a : A ⟶ B}
    {b : B ⟶ D} (p : D = D) {z : A ⟶ D} (h : a ≫ b = z) : a ≫ b ≫ eqToHom p = z := by
  have hp : p = rfl := rfl
  rw [hp, eqToHom_refl, Category.comp_id, h]

/-! ### The ideal sheaf of the completion chart -/

section Chart

/-- **The inverse image of `𝒥` along the completion chart of an affine open `U` is the ideal
sheaf attached to the extension of `𝒥(U)` to the `𝒥(U)`-adic completion of `Γ(Y, U)`.** This is
the identification which makes the complete affine case of Stacks 088B applicable over the
chart. -/
public lemma comap_adicCompletionChart {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData) (U : Y.affineOpens) :
    J.comap (adicCompletionChart J U) =
      baseIdealSheafOnSpec (adicCompletionSections J U)
        ((J.ideal U).map (algebraMap Γ(Y, U.1) (adicCompletionSections J U))) := by
  have hfrom : (J.comap U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((Scheme.ΓSpecIso Γ(Y, U.1)).inv).hom (J.ideal U) :=
    Stacks.Blowup.ideal_comap_fromSpec_top J U
  rw [adicCompletionChart, Scheme.IdealSheafData.comap_comp,
    comap_eq_ofIdealTop _ (J.comap U.2.fromSpec), hfrom]
  exact congrArg Scheme.IdealSheafData.ofIdealTop
    (Stacks.Blowup.map_appTop_map_ΓSpecIso_inv _ (J.ideal U))

/-- An affine chart `Spec A ⟶ U ⟶ Y` of an affine open lands in `U`. -/
private lemma top_le_preimage_spec_map_comp_fromSpec {Y : Scheme.{u}} (U : Y.affineOpens)
    {A : CommRingCat.{u}} (φ : Γ(Y, U.1) ⟶ A) :
    (⊤ : (Spec A).Opens) ≤ (Spec.map φ ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := by
  rw [Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
  exact le_top

/-- The map on sections of an affine chart `Spec A ⟶ U ⟶ Y` built from `φ : Γ(Y, U) ⟶ A`, read
through `Scheme.ΓSpecIso`, is `φ` itself. -/
private lemma appLE_spec_map_comp_fromSpec {Y : Scheme.{u}} (U : Y.affineOpens)
    {A : CommRingCat.{u}} (φ : Γ(Y, U.1) ⟶ A)
    (h : (⊤ : (Spec A).Opens) ≤ (Spec.map φ ≫ U.2.fromSpec) ⁻¹ᵁ U.1) :
    (Spec.map φ ≫ U.2.fromSpec).appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso A).hom = φ := by
  have e1 : (⊤ : (Spec Γ(Y, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 :=
    U.2.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Spec A).Opens) ≤ Spec.map φ ⁻¹ᵁ (⊤ : (Spec Γ(Y, U.1)).Opens) := le_top
  have h1 : U.2.fromSpec.appLE U.1 (⊤ : (Spec Γ(Y, U.1)).Opens) e1 =
      (Scheme.ΓSpecIso Γ(Y, U.1)).inv := by
    simp only [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    simp
  have h2 : (Spec.map φ).appLE (⊤ : (Spec Γ(Y, U.1)).Opens) (⊤ : (Spec A).Opens) e2 =
      (Spec.map φ).appTop := Scheme.Hom.appLE_eq_app _
  have hsplit := Scheme.Hom.appLE_comp_appLE (Spec.map φ) U.2.fromSpec U.1
    (⊤ : (Spec Γ(Y, U.1)).Opens) (⊤ : (Spec A).Opens) e1 e2
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.ΓSpecIso A).hom) hsplit.symm) ?_
  rw [h1, h2, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The completion chart of an affine open `U` lands in `U`. -/
public lemma top_le_preimage_adicCompletionChart {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData) (U : Y.affineOpens) :
    (⊤ : (Spec (CommRingCat.of (adicCompletionSections J U))).Opens) ≤
      adicCompletionChart J U ⁻¹ᵁ U.1 :=
  top_le_preimage_spec_map_comp_fromSpec U _

/-- **The completion chart induces the completion map on sections.** Read through
`Scheme.ΓSpecIso`, the map `Γ(Y, U) ⟶ Γ(Spec Γ(Y, U)^, ⊤)` of the completion chart is the
canonical map of `Γ(Y, U)` into its `𝒥(U)`-adic completion. This is the bookkeeping which lets
the equivalence on `𝒥(U)`-power torsion modules be read on the chart. -/
public lemma appLE_adicCompletionChart {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData) (U : Y.affineOpens)
    (h : (⊤ : (Spec (CommRingCat.of (adicCompletionSections J U))).Opens) ≤
      adicCompletionChart J U ⁻¹ᵁ U.1) :
    (adicCompletionChart J U).appLE U.1 ⊤ h ≫
        (Scheme.ΓSpecIso (CommRingCat.of (adicCompletionSections J U))).hom =
      CommRingCat.ofHom (algebraMap Γ(Y, U.1) (adicCompletionSections J U)) :=
  appLE_spec_map_comp_fromSpec U _ h

end Chart

/-! ### The base-change comparison for the completion of a direct image -/

section Square

variable {X Y X' Y' : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X']
  [IsNoetherian Y'] {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (w : g' ≫ f = f' ≫ g) (J : Y.IdealSheafData)
  (hJ : (J.comap f).comap g' = (J.comap g).comap f')
  (F : X.Modules) [F.IsCoherent]
  [((Scheme.Modules.pushforward f).obj F).IsCoherent]
  [((Scheme.Modules.pullback g').obj F).IsCoherent]
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent]

omit [AlgebraicGeometry.IsNoetherian Y] [((Scheme.Modules.pushforward f).obj F).IsCoherent] in
/-- `Stacks.Coherent.pullbackCompletionComparison_projection` restated so that the coherent
module `(g')^*𝓕` carries the ambient coherence instance. -/
private lemma pullback_map_completionProjection (k : ℕ) :
    (Scheme.Modules.pullback g').map
        (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k) ≫
      (pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom =
      Stacks.Algebraization.completionProjection X' ((J.comap f).comap g')
        ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k :=
  pullbackCompletionComparison_projection g' (J.comap f) ⟨F, inferInstance⟩ (op k)

omit [AlgebraicGeometry.IsNoetherian Y] [((Scheme.Modules.pushforward f).obj F).IsCoherent] in
/-- `Stacks.Coherent.completionProjection_pullbackCompletionTerm` for an arbitrary presentation
of the inverse-image ideal sheaf on the corner, so that the transport can be substituted away. -/
private lemma completionProjection_pullbackCompletionTerm_of_eq {L : X'.IdealSheafData}
    (hL : (J.comap f).comap g' = L) (k : ℕ) :
    (Scheme.Modules.pullback g').map
        (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k) ≫
      ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
        eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj.obj (op k)) hL)) =
      Stacks.Algebraization.completionProjection X' L
        ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k := by
  subst hL
  exact comp_comp_eqToHom_refl _ (pullback_map_completionProjection J F k)

omit [AlgebraicGeometry.IsNoetherian Y']
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent]
  [AlgebraicGeometry.IsNoetherian Y] [((Scheme.Modules.pushforward f).obj F).IsCoherent] in
/-- **The levelwise comparison `(g')^*(𝓕^) ⟶ (((g')^*𝓕)^)` is normalised by the projections.**
The identification `hJ` of the two inverse-image ideal sheaves of the corner is a parameter; for
a commuting square it is `Stacks.Coherent.comap_comap_of_comm`. -/
public lemma completionProjection_pullbackCompletionTerm (k : ℕ) :
    (Scheme.Modules.pullback g').map
        (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k) ≫
      ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
        eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj.obj (op k)) hJ)) =
      Stacks.Algebraization.completionProjection X' ((J.comap g).comap f')
        ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k :=
  completionProjection_pullbackCompletionTerm_of_eq J F hJ k

/-- **The base-change comparison for the completion of a direct image**: from the inverse image
along `g` of the completion of `f_*𝓕` to the completion of `f'_*((g')^*𝓕)`. -/
public def pushforwardCompletionBaseChange :
    ((Stacks.Algebraization.completionFunctor Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj ⋙
        Scheme.Modules.pullback g ⟶
      ((Stacks.Algebraization.completionFunctor Y' (J.comap g)).obj
        ⟨(Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
          inferInstance⟩).obj :=
  (pullbackCompletionIso g J ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).hom.hom ≫
    ((Stacks.Algebraization.completionFunctor Y' (J.comap g)).map
      (ObjectProperty.homMk
        (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w F))).hom

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian X'] [F.IsCoherent]
  [((Scheme.Modules.pullback g').obj F).IsCoherent] in
/-- The components of `Stacks.Coherent.pushforwardCompletionBaseChange`. -/
public lemma pushforwardCompletionBaseChange_app (n : ℕᵒᵖ) :
    (pushforwardCompletionBaseChange w J F).app n =
      (pullbackCompletionComparison g J
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ n).hom ≫
        ((Stacks.Algebraization.completionFunctor Y' (J.comap g)).map
          (ObjectProperty.homMk
            (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w F))).hom.app n :=
  rfl

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian X'] [F.IsCoherent]
  [((Scheme.Modules.pullback g').obj F).IsCoherent] in
/-- The base-change comparison carries the projection of `f_*𝓕` onto the `k`-th term of its
completion to the projection of `f'_*((g')^*𝓕)`. -/
private lemma projection_comp_pushforwardCompletionBaseChange (k : ℕ) :
    (Scheme.Modules.pullback g).map (Stacks.Algebraization.completionProjection Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k) ≫
      (pushforwardCompletionBaseChange w J F).app (op k) =
      Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w F ≫
        Stacks.Algebraization.completionProjection Y' (J.comap g)
          ⟨(Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
            inferInstance⟩ k :=
  (congrArg (fun t => (Scheme.Modules.pullback g).map
        (Stacks.Algebraization.completionProjection Y J
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k) ≫ t)
      (pushforwardCompletionBaseChange_app w J F (op k))).trans
    ((comp_left (pullbackCompletionComparison_projection g J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ (op k))).trans
      (Stacks.Algebraization.completionFunctor_map_quotient Y' (J.comap g) _ k))

omit [AlgebraicGeometry.IsNoetherian X] [F.IsCoherent] in
/-- The left-hand composite of `Stacks.Coherent.pushforwardCompletionBaseChange_comp_comparison`,
after the projection of `f_*𝓕` has been cancelled. -/
private lemma projection_comp_left (k : ℕ) :
    (Scheme.Modules.pullback g).map (Stacks.Algebraization.completionProjection Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k) ≫
      ((pushforwardCompletionBaseChange w J F).app (op k) ≫
        (pushforwardCompletionComparison f' (J.comap g)
          ((Scheme.Modules.pullback g').obj F)).app (op k)) =
      Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w F ≫
        (Scheme.Modules.pushforward f').map
          (Stacks.Algebraization.completionProjection X' ((J.comap g).comap f')
            ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k) :=
  (comp_left (projection_comp_pushforwardCompletionBaseChange w J F k)).trans
    (comp_right (pushforwardCompletionComponent_π f' (J.comap g)
      ((Scheme.Modules.pullback g').obj F) k))

omit [AlgebraicGeometry.IsNoetherian Y'] in
/-- The inverse image along `g` of the comparison map of `f_*𝓕`, precomposed with the inverse
image of the projection. -/
private lemma pullback_map_pushforwardCompletionComparison (k : ℕ) :
    (Scheme.Modules.pullback g).map (Stacks.Algebraization.completionProjection Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k) ≫
      (Scheme.Modules.pullback g).map
        ((pushforwardCompletionComparison f J F).app (op k)) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map
        (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k)) :=
  map_comp_of_comp_eq _ (pushforwardCompletionComponent_π f J F k)

omit [AlgebraicGeometry.IsNoetherian Y']
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent]
  [AlgebraicGeometry.IsNoetherian Y] [((Scheme.Modules.pushforward f).obj F).IsCoherent] in
/-- The direct image under `f'` of
`Stacks.Coherent.completionProjection_pullbackCompletionTerm`. -/
private lemma pushforward_map_completionTerm (k : ℕ) :
    (Scheme.Modules.pushforward f').map ((Scheme.Modules.pullback g').map
        (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k)) ≫
      (Scheme.Modules.pushforward f').map
        ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
          eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
            ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj.obj (op k)) hJ)) =
      (Scheme.Modules.pushforward f').map
        (Stacks.Algebraization.completionProjection X' ((J.comap g).comap f')
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k) :=
  map_comp_of_comp_eq _ (completionProjection_pullbackCompletionTerm J hJ F k)

omit [AlgebraicGeometry.IsNoetherian Y']
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent]
  [AlgebraicGeometry.IsNoetherian Y] [((Scheme.Modules.pushforward f).obj F).IsCoherent] in
/-- The level-`k` base-change comparison carries the inverse image of the direct image of the
projection of `𝓕` to the direct image of the projection of `(g')^*𝓕`. -/
private lemma pushforward_projection_comp_completionTermBaseChange (k : ℕ) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map
          (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k)) ≫
        (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
            (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
              ⟨F, inferInstance⟩).obj.obj (op k)) ≫
          (Scheme.Modules.pushforward f').map
            ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
              eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
                ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj.obj (op k)) hJ))) =
      Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w F ≫
        (Scheme.Modules.pushforward f').map
          (Stacks.Algebraization.completionProjection X' ((J.comap g).comap f')
            ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k) :=
  (comp_left (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality w
      (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ k))).trans
    (comp_right (pushforward_map_completionTerm J hJ F k))

omit [AlgebraicGeometry.IsNoetherian Y']
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent] in
/-- The right-hand composite of `Stacks.Coherent.pushforwardCompletionBaseChange_comp_comparison`,
after the projection of `f_*𝓕` has been cancelled. -/
private lemma projection_comp_right (k : ℕ) :
    (Scheme.Modules.pullback g).map (Stacks.Algebraization.completionProjection Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k) ≫
      ((Scheme.Modules.pullback g).map
          ((pushforwardCompletionComparison f J F).app (op k)) ≫
        (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
            (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
              ⟨F, inferInstance⟩).obj.obj (op k)) ≫
          (Scheme.Modules.pushforward f').map
            ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
              eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
                ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj.obj (op k)) hJ)))) =
      Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w F ≫
        (Scheme.Modules.pushforward f').map
          (Stacks.Algebraization.completionProjection X' ((J.comap g).comap f')
            ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩ k) :=
  (comp_left (pullback_map_pushforwardCompletionComparison J F k)).trans
    (pushforward_projection_comp_completionTermBaseChange w J hJ F k)

/-- **The base-change comparison intertwines the two comparison maps of a completed direct
image.** Both sides are determined by their composite with the projection of `f_*𝓕` onto the
`k`-th term of its completion, which becomes an epimorphism after inverse image along `g`, and
there both become the direct image under `f'` of the projection of `(g')^*𝓕`.

The right-hand side is the inverse image along `g` of the comparison of `f_*𝓕`, followed by the
degree-zero base-change comparison at the `k`-th term of the completion of `𝓕` and by the direct
image of the levelwise comparison of
`Stacks.Coherent.completionProjection_pullbackCompletionTerm`. -/
public lemma pushforwardCompletionBaseChange_comp_comparison (k : ℕ) :
    (pushforwardCompletionBaseChange w J F).app (op k) ≫
        (pushforwardCompletionComparison f' (J.comap g)
          ((Scheme.Modules.pullback g').obj F)).app (op k) =
      (Scheme.Modules.pullback g).map
          ((pushforwardCompletionComparison f J F).app (op k)) ≫
        (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
            (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
              ⟨F, inferInstance⟩).obj.obj (op k)) ≫
          (Scheme.Modules.pushforward f').map
            ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
              eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
                ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj.obj (op k)) hJ))) := by
  have hpe : (Scheme.Modules.pullback g).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction g)
  have hep : Epi (C := Y.Modules) (Stacks.Algebraization.completionProjection Y J
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k) :=
    epi_completionProjection J ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k
  have hepi : Epi (C := Y'.Modules) ((Scheme.Modules.pullback g).map
      (Stacks.Algebraization.completionProjection Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ k)) :=
    @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback g) hpe _ _ _ hep
  exact hepi.left_cancellation _ _
    ((projection_comp_left w J F k).trans (projection_comp_right w J hJ F k).symm)

end Square

section Datum

variable {X Y X' Y' : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X']
  [IsNoetherian Y'] {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (w : g' ≫ f = f' ≫ g) (J : Y.IdealSheafData)
  (hJ : (J.comap f).comap g' = (J.comap g).comap f')
  (G : CoherentAdicSystems J)
  (F : X.Modules) [F.IsCoherent] [((Scheme.Modules.pullback g').obj F).IsCoherent]
  [((Scheme.Modules.pushforward f).obj F).IsCoherent]
  [((Scheme.Modules.pushforward f').obj
    ((Scheme.Modules.pullback g').obj F)).IsCoherent]
  (β : (coherentAdicPullback f J).obj G ≅
    (Stacks.Algebraization.completionFunctor X (J.comap f)).obj ⟨F, inferInstance⟩)

/-- The underlying natural isomorphism of `Stacks.Coherent.baseChangeDatumIso`, with the
inverse-image ideal sheaf of the corner left as a parameter so that the transport can be
substituted away. -/
public def baseChangeDatumSystemIso {L : X'.IdealSheafData}
    (hL : (J.comap f).comap g' = L) :
    ((coherentAdicPullback g J).obj G).obj ⋙ Scheme.Modules.pullback f' ≅
      ((Stacks.Algebraization.completionFunctor X' L).obj
        ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩).obj :=
  Functor.isoWhiskerLeft G.obj
      (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareNatIso w).symm ≪≫
    Functor.isoWhiskerRight ((ObjectProperty.ι (IsCoherentAdicSystem (J.comap f))).mapIso β)
      (Scheme.Modules.pullback g') ≪≫
    (ObjectProperty.ι (IsCoherentAdicSystem ((J.comap f).comap g'))).mapIso
      (pullbackCompletionIso g' (J.comap f) ⟨F, inferInstance⟩) ≪≫
    completionSystemCongr hL (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩)

omit [((Scheme.Modules.pushforward f).obj F).IsCoherent]
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent] in
/-- The components of `Stacks.Coherent.baseChangeDatumSystemIso`. -/
public lemma baseChangeDatumSystemIso_hom_app {L : X'.IdealSheafData}
    (hL : (J.comap f).comap g' = L) (n : ℕᵒᵖ) :
    (baseChangeDatumSystemIso w J G F β hL).hom.app n =
      (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareNatIso w).inv.app
          (G.obj.obj n) ≫
        (Scheme.Modules.pullback g').map (β.hom.hom.app n) ≫
        (pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ n).hom ≫
        eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
          (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩)).obj.obj n) hL) := by
  subst hL
  rfl

/-- **The isomorphism `β` of Stacks 088B, transported along a commuting square.** It is the
canonical identification of the two composite inverse images around the square, followed by the
inverse image along `g'` of `β` and by the comparison of inverse image with completion. -/
public def baseChangeDatumIso :
    (coherentAdicPullback f' (J.comap g)).obj ((coherentAdicPullback g J).obj G) ≅
      (Stacks.Algebraization.completionFunctor X' ((J.comap g).comap f')).obj
        (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩) :=
  ObjectProperty.isoMk _ (baseChangeDatumSystemIso w J G F β hJ)

omit [((Scheme.Modules.pushforward f).obj F).IsCoherent]
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent] in
/-- The components of `Stacks.Coherent.baseChangeDatumIso`. -/
public lemma baseChangeDatumIso_hom_app (n : ℕᵒᵖ) :
    (baseChangeDatumIso w J hJ G F β).hom.hom.app n =
      (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareNatIso w).inv.app
          (G.obj.obj n) ≫
        (Scheme.Modules.pullback g').map (β.hom.hom.app n) ≫
        (pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ n).hom ≫
        eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
          (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩)).obj.obj n) hJ) :=
  baseChangeDatumSystemIso_hom_app w J G F β hJ n

omit [((Scheme.Modules.pushforward f).obj F).IsCoherent]
  [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent] in
/-- **The base-change comparison carries the maps `γ` of Stacks 088B to the maps `γ` of the
transported datum.** The two factors of `γ` are handled separately: the adjunction map by
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_unit`, and the factor `f_*β` by
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality`. -/
public lemma directImageComparison_baseChange (k : ℕ) :
    (Scheme.Modules.pullback g).map
        ((directImageComparison f J G ⟨F, inferInstance⟩ β).app (op k)) ≫
      (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
          (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
              ⟨F, inferInstance⟩).obj.obj (op k)) ≫
        (Scheme.Modules.pushforward f').map
          ((pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
            eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
              (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩)).obj.obj (op k)) hJ))) =
      (directImageComparison f' (J.comap g) ((coherentAdicPullback g J).obj G)
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩
            (baseChangeDatumIso w J hJ G F β)).app (op k) := by
  have hmidR : (directImageComparison f' (J.comap g) ((coherentAdicPullback g J).obj G)
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩
            (baseChangeDatumIso w J hJ G F β)).app (op k) =
      (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj (op k))) ≫
        (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
            ((Scheme.Modules.pullback f).obj (G.obj.obj (op k))) ≫
          (Scheme.Modules.pushforward f').map
            ((Scheme.Modules.pullback g').map (β.hom.hom.app (op k)) ≫
              (pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
                eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
                  (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩)).obj.obj (op k)) hJ))) :=
    (directImageComparison_app f' (J.comap g) ((coherentAdicPullback g J).obj G)
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩
            (baseChangeDatumIso w J hJ G F β) (op k)).trans
      ((congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
            (((coherentAdicPullback g J).obj G).obj.obj (op k)) ≫ t)
          ((congrArg (Scheme.Modules.pushforward f').map
              (baseChangeDatumIso_hom_app w J hJ G F β (op k))).trans
            ((Scheme.Modules.pushforward f').map_comp _ _))).trans
        ((congrArg (fun t => t ≫ ((Scheme.Modules.pushforward f').map
              (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso w
                (G.obj.obj (op k))).inv ≫
            (Scheme.Modules.pushforward f').map
              ((Scheme.Modules.pullback g').map (β.hom.hom.app (op k)) ≫
                (pullbackCompletionComparison g' (J.comap f) ⟨F, inferInstance⟩ (op k)).hom ≫
                  eqToHom (congrArg (fun T => ((Stacks.Algebraization.completionFunctor X' T).obj
                    (⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩)).obj.obj (op k)) hJ))))
            (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_unit w
              (G.obj.obj (op k))).symm).trans
          (comp_comp_cancel _ _ (map_hom_comp_map_inv_comp (Scheme.Modules.pushforward f')
            (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso w
              (G.obj.obj (op k))) _))))
  rw [hmidR, directImageComparison_app f J G ⟨F, inferInstance⟩ β (op k), Functor.map_comp]
  exact comp_right ((comp_left
      (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality w
        (β.hom.hom.app (op k)))).trans
    (comp_right (map_comp_of_comp_eq _ rfl)))

/-- **The defining equation of the comparison map of Stacks 088B survives the transport.** The
transported map is the inverse image of `α` followed by the base-change comparison for the
completion of the direct image; its composite with the comparison map of `f'` is the `γ` of the
transported datum, by the two squares
`Stacks.Coherent.pushforwardCompletionBaseChange_comp_comparison` and
`Stacks.Coherent.directImageComparison_baseChange`. -/
public lemma systemMap_baseChange_comp_comparison
    (α : G ⟶ (Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩)
    (hα : α.hom ≫ pushforwardCompletionComparison f J F =
      directImageComparison f J G ⟨F, inferInstance⟩ β) :
    ((coherentAdicPullback g J).map α ≫
          ObjectProperty.homMk (pushforwardCompletionBaseChange w J F)).hom ≫
        pushforwardCompletionComparison f' (J.comap g)
          ((Scheme.Modules.pullback g').obj F) =
      directImageComparison f' (J.comap g) ((coherentAdicPullback g J).obj G)
          ⟨(Scheme.Modules.pullback g').obj F, inferInstance⟩
            (baseChangeDatumIso w J hJ G F β) := by
  refine NatTrans.ext (funext fun n => ?_)
  obtain ⟨k⟩ := n
  exact (comp_right (pushforwardCompletionBaseChange_comp_comparison w J hJ F k)).trans
    ((comp_left ((Scheme.Modules.pullback g).map_comp _ _).symm).trans
      ((congrArg (fun t => (Scheme.Modules.pullback g).map t ≫
            (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
                (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
                    ⟨F, inferInstance⟩).obj.obj (op k)) ≫
              (Scheme.Modules.pushforward f').map
                ((pullbackCompletionComparison g' (J.comap f)
                    ⟨F, inferInstance⟩ (op k)).hom ≫
                  eqToHom (congrArg (fun T =>
                    ((Stacks.Algebraization.completionFunctor X' T).obj
                      ⟨(Scheme.Modules.pullback g').obj F,
                        inferInstance⟩).obj.obj (op k)) hJ))))
          (NatTrans.congr_app hα (op k))).trans
        (directImageComparison_baseChange w J hJ G F β k)))

end Datum

/-! ### The complete affine case at a presented ideal sheaf -/

/-- **The kernel–cokernel bound over a complete affine base, with the ideal sheaf presented as a
parameter.** This is `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_isAdicComplete` with
the identification of the base ideal sheaf with `Stacks.Coherent.baseIdealSheafOnSpec`
substituted away, which is the form in which the completion chart supplies it. -/
public theorem isKernelCokernelAnnihilatedByPower_of_eq_baseIdealSheafOnSpec
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : (Spec (.of A)).IdealSheafData) (hL : L = baseIdealSheafOnSpec A I)
    (K : (Spec (.of A)).IdealSheafData) (hf : IsIso (f ∣_ K.support.compl))
    (G : CoherentAdicSystems L) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ (β : (coherentAdicPullback f L).obj G ≅
        (Stacks.Algebraization.completionFunctor X (L.comap f)).obj ⟨F, inferInstance⟩)
      (α : G ⟶ (Stacks.Algebraization.completionFunctor (Spec (.of A)) L).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩),
      α.hom ≫ pushforwardCompletionComparison f L F =
          directImageComparison f L G ⟨F, inferInstance⟩ β →
        Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower K α.hom := by
  subst hL
  exact isKernelCokernelAnnihilatedByPower_of_isAdicComplete A I f K hf G F

/-! ### Reflecting the annihilation through a flat inverse image -/

/-- **The levelwise kernel and cokernel of a flat inverse image.** If the kernel and cokernel of
the inverse image of `a` along a flat `g`, composed with an isomorphism, are annihilated by
`𝒦' ᵗ`, then so are the inverse images of the kernel and cokernel of `a`.

Flatness makes the inverse image preserve kernels, and it preserves cokernels because it is a
left adjoint; composing with an isomorphism changes neither. -/
public lemma idealPowerMultiple_pullback_eq_bot_of_comp_iso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [Flat g] (K' : Y'.IdealSheafData) (t : ℕ) {M N : Y.Modules} (a : M ⟶ N)
    {P : Y'.Modules} (e : (Scheme.Modules.pullback g).obj N ⟶ P) [IsIso e]
    (hker : Stacks.Algebraization.idealPowerMultiple K' t
      (kernel ((Scheme.Modules.pullback g).map a ≫ e)) = ⊥)
    (hcok : Stacks.Algebraization.idealPowerMultiple K' t
      (cokernel ((Scheme.Modules.pullback g).map a ≫ e)) = ⊥) :
    Stacks.Algebraization.idealPowerMultiple K' t
        ((Scheme.Modules.pullback g).obj (kernel a)) = ⊥ ∧
      Stacks.Algebraization.idealPowerMultiple K' t
        ((Scheme.Modules.pullback g).obj (cokernel a)) = ⊥ := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback g) :=
    AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat g
  have : PreservesColimits (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  refine ⟨Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso K'
      (PreservesKernel.iso (Scheme.Modules.pullback g) a ≪≫
        (kernelCompMono ((Scheme.Modules.pullback g).map a) e).symm) t hker,
    Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso K'
      (PreservesCokernel.iso (Scheme.Modules.pullback g) a ≪≫
        (cokernelCompIsIso ((Scheme.Modules.pullback g).map a) e).symm) t hcok⟩

/-! ### Annihilation over an affine open, and over a kernel or a cokernel -/

/-- **On an affine scheme every quasi-coherent sheaf of ideals is the one attached to its ideal
of global sections.** This is `Stacks.Coherent.comap_eq_ofIdealTop` at the identity. -/
private lemma eq_ofIdealTop_ideal_top {Z : Scheme.{u}} [IsAffine Z] (L : Z.IdealSheafData) :
    L = Scheme.IdealSheafData.ofIdealTop (L.ideal ⟨⊤, isAffineOpen_top Z⟩) := by
  have h := comap_eq_ofIdealTop (𝟙 Z) L
  rw [Scheme.IdealSheafData.comap_id] at h
  refine h.trans (congrArg Scheme.IdealSheafData.ofIdealTop ?_)
  simp

/-- **Annihilation of the restriction to an affine open, from annihilation of the sections over
it.** On an affine open `U` of `Y` the sections of a quasi-coherent module over the whole of `U`
determine the module, so one power of `𝒦(U)` annihilating them annihilates `𝒦|_U ᵗ (𝓕|_U)`.

`Stacks.Coherent.affine_idealPowerMultiple_eq_bot` presents the sections over the top open of `U`
as the sections over the image `U.ι ''ᵁ ⊤`, which is `U` only up to an equality of opens that no
rewrite inside the types can use; the hypothesis is therefore first generalised to the affine
opens *equal* to `U`, and that equality substituted away. -/
private lemma idealPowerMultiple_comap_ι_eq_bot_of_affine {Y : Scheme.{u}}
    (K : Y.IdealSheafData) (t : ℕ) (U : Y.affineOpens) (M : Y.Modules) [M.IsQuasicoherent]
    (h : ∀ r ∈ K.ideal U ^ t, ∀ x : Γ(M, U.1), r • x = 0) :
    Stacks.Algebraization.idealPowerMultiple (K.comap U.1.ι) t
      ((Scheme.Modules.restrictFunctor U.1.ι).obj M) = ⊥ := by
  have := U.2
  have := Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι M
  have hgen : ∀ V : Y.affineOpens, V = U →
      ∀ r ∈ K.ideal V ^ t, ∀ x : Γ(M, V.1), r • x = 0 := by
    rintro V rfl
    exact h
  rw [eq_ofIdealTop_ideal_top (K.comap U.1.ι)]
  refine affine_idealPowerMultiple_eq_bot _ t _ ?_
  rw [Stacks.Algebraization.ideal_smul_top_eq_bot_iff]
  intro r hr x
  have hVa : IsAffineOpen (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι
  have hVU : (⟨U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens), hVa⟩ : Y.affineOpens) = U :=
    Subtype.ext U.1.ι_image_top
  have hp : Ideal.comap (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv.hom
        (K.ideal ⟨U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens), hVa⟩) ^ t =
      Ideal.comap (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv.hom
        (K.ideal ⟨U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens), hVa⟩ ^ t) := by
    change Ideal.comap
      (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).commRingCatIsoToRingEquiv.symm _ ^ t =
        Ideal.comap
          (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).commRingCatIsoToRingEquiv.symm _
    rw [← Ideal.map_comap_of_equiv
        (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).commRingCatIsoToRingEquiv,
      ← Ideal.map_comap_of_equiv
        (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).commRingCatIsoToRingEquiv, Ideal.map_pow]
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, hp] at hr
  exact hgen _ hVU _ hr x

/-- **Annihilation by a power of an ideal sheaf passes to a kernel.** A monomorphism of sheaves
of modules is injective on the sections over every open. -/
private lemma idealPowerMultiple_kernel_eq_bot {Z : Scheme.{u}} (L : Z.IdealSheafData) (n : ℕ)
    {M N : Z.Modules} (a : M ⟶ N)
    (hM : Stacks.Algebraization.idealPowerMultiple L n M = ⊥) :
    Stacks.Algebraization.idealPowerMultiple L n (kernel (C := Z.Modules) a) = ⊥ := by
  refine Stacks.Algebraization.idealPowerMultiple_eq_bot_of_affine_sections_annihilated
    fun V r hr x => ?_
  refine Stacks.Algebraization.app_injective_of_mono (kernel.ι (C := Z.Modules) a)
    inferInstance V.1 ?_
  rw [Scheme.Modules.Hom.app_smul, map_zero]
  exact Stacks.Algebraization.affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM V hr _

/-! ### Descent of the annihilation from the completion chart -/

/-- **The annihilation of the sections over an affine open descends from the completion chart.**
Let `U` be an affine open of `Y` and `𝓕` a quasi-coherent `𝒪_Y`-module annihilated by a power of
`𝒥`. If `(𝒦.comap c) ᵗ` annihilates the inverse image of `𝓕` along the completion chart
`c : Spec Γ(Y, U)^ ⟶ Y`, then `𝒦(U) ᵗ` annihilates `Γ(𝓕, U)`.

The comparison on sections is `AlgebraicGeometry.Scheme.Modules.pullbackSection` over the single
pair of affine opens `(U, ⊤)`; it is semilinear over
`(c.appLE U ⊤)`, which `Stacks.Coherent.appLE_adicCompletionChart` identifies with the completion
map of `Γ(Y, U)`, and it has trivial kernel because `Γ(Y, U) ⟶ Γ(Y, U)^` is an equivalence on the
modules annihilated by a power of `𝒥(U)`
(`tensorProduct_mk_bijective_of_ideal_power_torsion`). -/
private lemma smul_eq_zero_of_chart {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J K : Y.IdealSheafData) (U : Y.affineOpens) (t : ℕ) (M : Y.Modules) [M.IsQuasicoherent]
    (hM : Stacks.Algebraization.IsPowerAnnihilated J M)
    (hpull : Stacks.Algebraization.idealPowerMultiple (K.comap (adicCompletionChart J U)) t
      ((Scheme.Modules.pullback (adicCompletionChart J U)).obj M) = ⊥)
    {r : Γ(Y, U.1)} (hr : r ∈ K.ideal U ^ t) (a : Γ(M, U.1)) : r • a = 0 := by
  have hnr : IsNoetherianRing Γ(Y, U.1) := isNoetherianRing_sections U
  have hVU := top_le_preimage_adicCompletionChart J U
  let : Algebra Γ(Y, U.1)
      Γ(Spec (CommRingCat.of (adicCompletionSections J U)), (⊤ : _)) :=
    ((adicCompletionChart J U).appLE U.1 ⊤ hVU).hom.toAlgebra
  have halg : (Scheme.ΓSpecIso
          (CommRingCat.of (adicCompletionSections J U))).commRingCatIsoToRingEquiv.toRingHom.comp
        (algebraMap Γ(Y, U.1)
          Γ(Spec (CommRingCat.of (adicCompletionSections J U)), (⊤ : _))) =
      algebraMap Γ(Y, U.1) (adicCompletionSections J U) :=
    (CommRingCat.hom_comp _ _).symm.trans
      (congrArg CommRingCat.Hom.hom (appLE_adicCompletionChart J U hVU))
  have hQ : ∀ n : ℕ, 0 < n → Function.Bijective (Ideal.quotientMap
      (Ideal.map (algebraMap Γ(Y, U.1)
        Γ(Spec (CommRingCat.of (adicCompletionSections J U)), (⊤ : _))) (J.ideal U ^ n))
      (algebraMap Γ(Y, U.1)
        Γ(Spec (CommRingCat.of (adicCompletionSections J U)), (⊤ : _)))
      Ideal.le_comap_map) := by
    intro n _
    refine Rig.bijective_quotientMap_pow_of_ringEquiv _
      (Scheme.ΓSpecIso
        (CommRingCat.of (adicCompletionSections J U))).commRingCatIsoToRingEquiv
      (J.ideal U) n ?_
    rw [halg]
    exact Rig.bijective_quotientMap_pow_algebraMap_adicCompletion (J.ideal U)
      (Ideal.fg_of_isNoetherianRing _) n
  have htors : ∀ x : Γ(M, U.1), ∃ n : ℕ, ∀ s ∈ J.ideal U ^ n, s • x = 0 := fun x => by
    obtain ⟨n, _, hn⟩ :=
      Stacks.Algebraization.isIPowerTorsion_sections_of_isPowerAnnihilated hM U x
    exact ⟨n, hn⟩
  have hone := IPowerTorsion.one_tmul_bijective
    ((_root_.tensorProduct_mk_bijective_of_ideal_power_torsion.{u, u, u} Γ(Y, U.1)
      (J.ideal U) Γ(M, U.1) htors).1
      Γ(Spec (CommRingCat.of (adicCompletionSections J U)), (⊤ : _)) hQ)
  refine smul_eq_zero_of_injective_sectionsComparison (adicCompletionChart J U) M K t U
    ⟨⊤, isAffineOpen_top _⟩ hVU
    (Scheme.Modules.pullbackSection (adicCompletionChart J U) M U.1 ⊤ hVU)
    (fun s x => AlgebraicGeometry.pullbackSectionHom_smul (adicCompletionChart J U) M U.1 ⊤
      hVU s x)
    (fun x hx => ?_) hpull hr a
  have he := AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul
    (adicCompletionChart J U) M U.2 (isAffineOpen_top _) hVU x
  have hinj : Function.Injective (ModuleCat.Hom.hom
      (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso (adicCompletionChart J U) M U.2
        (isAffineOpen_top _) hVU).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have h0 := hinj ((he.trans hx).trans (map_zero _).symm)
  refine hone.1 (Eq.trans ?_ (map_zero _).symm)
  refine (IPowerTorsion.tensorModuleCatEquiv.{u, u, u}
    (S := Γ(Spec (CommRingCat.of (adicCompletionSections J U)), (⊤ : _)))
    (ModuleCat.of Γ(Y, U.1) Γ(M, U.1))).injective ?_
  exact (IPowerTorsion.tensorModuleCatEquiv_tmul _ _ _).trans
    (h0.trans (map_zero _).symm)

/-! ### The bound over an affine open of the base -/

section ChartBound

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (J K : Y.IdealSheafData)
  (f : X ⟶ Y) [IsProper f] (G : CoherentAdicSystems J) (F : X.Modules) [F.IsCoherent]
  [((Scheme.Modules.pushforward f).obj F).IsCoherent]

/-- **The levelwise kernels and cokernels of `α`, pulled back along the completion chart of an
affine open `U`, are annihilated by one power of `𝒦`.** This is the complete affine case of
Stacks 088B applied to the datum transported along the chart, read back through the flatness of
the chart by `Stacks.Coherent.idealPowerMultiple_pullback_eq_bot_of_comp_iso`. -/
private lemma exists_idealPowerMultiple_pullback_chart_eq_bot
    (hf : IsIso (f ∣_ K.support.compl)) (U : Y.affineOpens)
    (β : (coherentAdicPullback f J).obj G ≅
      (Stacks.Algebraization.completionFunctor X (J.comap f)).obj ⟨F, inferInstance⟩)
    (α : G ⟶ (Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩)
    (hα : α.hom ≫ pushforwardCompletionComparison f J F =
      directImageComparison f J G ⟨F, inferInstance⟩ β) :
    ∃ t : ℕ, ∀ k : ℕ,
      Stacks.Algebraization.idealPowerMultiple (K.comap (adicCompletionChart J U)) t
          ((Scheme.Modules.pullback (adicCompletionChart J U)).obj
            (kernel (C := Y.Modules) (α.hom.app (op k)))) = ⊥ ∧
        Stacks.Algebraization.idealPowerMultiple (K.comap (adicCompletionChart J U)) t
          ((Scheme.Modules.pullback (adicCompletionChart J U)).obj
            (cokernel (C := Y.Modules) (α.hom.app (op k)))) = ⊥ := by
  have hflat : Flat (adicCompletionChart J U) := flat_adicCompletionChart J U
  have : IsNoetherianRing (adicCompletionSections J U) :=
    isNoetherianRing_adicCompletionSections J U
  have : IsAdicComplete
      ((J.ideal U).map (algebraMap Γ(Y, U.1) (adicCompletionSections J U)))
      (adicCompletionSections J U) :=
    isAdicComplete_adicCompletionSections J U
  have : IsNoetherian (Spec (CommRingCat.of (adicCompletionSections J U))) :=
    isNoetherian_specAdicCompletionSections J U
  have : IsNoetherian (Limits.pullback f (adicCompletionChart J U)) :=
    isNoetherian_of_isProper (Limits.pullback.snd f (adicCompletionChart J U))
  have : ((Scheme.Modules.pullback
      (Limits.pullback.fst f (adicCompletionChart J U))).obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback (Limits.pullback.fst f (adicCompletionChart J U)) F
  have : ((Scheme.Modules.pushforward (Limits.pullback.snd f (adicCompletionChart J U))).obj
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (adicCompletionChart J U))).obj F)).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward
      (Limits.pullback.snd f (adicCompletionChart J U)) _
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have w : Limits.pullback.fst f (adicCompletionChart J U) ≫ f =
      Limits.pullback.snd f (adicCompletionChart J U) ≫ adicCompletionChart J U :=
    Limits.pullback.condition
  have hJ := comap_comap_of_comm w J
  obtain ⟨t, _, hkc⟩ := isKernelCokernelAnnihilatedByPower_of_eq_baseIdealSheafOnSpec
    (adicCompletionSections J U)
    ((J.ideal U).map (algebraMap Γ(Y, U.1) (adicCompletionSections J U)))
    (Limits.pullback.snd f (adicCompletionChart J U))
    (J.comap (adicCompletionChart J U)) (comap_adicCompletionChart J U)
    (K.comap (adicCompletionChart J U))
    (isIso_morphismRestrict_pullback_snd f (adicCompletionChart J U) K hf)
    ((coherentAdicPullback (adicCompletionChart J U) J).obj G)
    ((Scheme.Modules.pullback (Limits.pullback.fst f (adicCompletionChart J U))).obj F)
    (baseChangeDatumIso w J hJ G F β)
    ((coherentAdicPullback (adicCompletionChart J U) J).map α ≫
      ObjectProperty.homMk (pushforwardCompletionBaseChange w J F))
    (systemMap_baseChange_comp_comparison w J hJ G F β α hα)
  refine ⟨t, fun k => ?_⟩
  have : IsIso ((pushforwardCompletionBaseChange w J F).app (op k)) :=
    NatIso.isIso_app_of_isIso (C := ℕᵒᵖ)
      (pushforwardCompletionBaseChangeIso f (adicCompletionChart J U) J
        ⟨F, inferInstance⟩).hom.hom (op k)
  exact idealPowerMultiple_pullback_eq_bot_of_comp_iso (adicCompletionChart J U)
    (K.comap (adicCompletionChart J U)) t (α.hom.app (op k))
    ((pushforwardCompletionBaseChange w J F).app (op k)) (hkc k).1 (hkc k).2

end ChartBound

/-! ### The kernel–cokernel bound over an arbitrary Noetherian base -/

/-- **The kernel–cokernel bound of Stacks 088B over an arbitrary Noetherian base.** Let `Y` be a
Noetherian scheme, `𝒥, 𝒦 ⊆ 𝒪_Y` quasi-coherent sheaves of ideals, `f : X ⟶ Y` proper and an
isomorphism over `Y ∖ V(𝒦)`, `(𝒢_n)` a coherent `𝒥`-adic system, `𝓕` a coherent `𝒪_X`-module and
`β : (f^*𝒢_n) ≅ 𝓕^` an isomorphism. Then the levelwise kernels and cokernels of any map
`α : (𝒢_n) ⟶ (f_*𝓕)^` satisfying the defining equation `α ≫ c = γ` are annihilated by one power
of `𝒦`.

The bound is local on `Y`, so it suffices to produce one exponent per affine open `U`
(`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_restrict`). Over `U` the whole datum is
base changed along the flat completion chart `Spec Γ(Y, U)^ ⟶ Y`, where the base is the spectrum
of a Noetherian ring complete along the extension of `𝒥(U)` and the complete affine case applies;
flatness of the chart reflects the resulting annihilation to the inverse images of the kernels and
cokernels, and the equivalence of `Γ(Y, U)` with its completion on `𝒥(U)`-power torsion modules
descends it to the sections over `U`. -/
public theorem isKernelCokernelAnnihilatedByPower_of_isNoetherian
    {X Y : Scheme.{u}} [IsNoetherian Y] (J K : Y.IdealSheafData)
    (f : X ⟶ Y) [IsProper f] (hf : IsIso (f ∣_ K.support.compl))
    (G : CoherentAdicSystems J) (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ (β : (coherentAdicPullback f J).obj G ≅
        (Stacks.Algebraization.completionFunctor X (J.comap f)).obj ⟨F, inferInstance⟩)
      (α : G ⟶ (Stacks.Algebraization.completionFunctor Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩),
      α.hom ≫ pushforwardCompletionComparison f J F =
          directImageComparison f J G ⟨F, inferInstance⟩ β →
        Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower K α.hom := by
  intro β α hα
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  refine isKernelCokernelAnnihilatedByPower_of_restrict K α.hom fun U => ?_
  obtain ⟨t, hT⟩ :=
    exists_idealPowerMultiple_pullback_chart_eq_bot J K f G F hf U β α hα
  refine ⟨t, fun k => ?_⟩
  have hGk : (G.obj.obj (op k)).IsCoherent := G.property.1 k
  have hCk : (((Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj.obj (op k)).IsCoherent :=
    ((Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).property.1 k
  have : (kernel (C := Y.Modules) (α.hom.app (op k))).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (α.hom.app (op k))
  have : (cokernel (C := Y.Modules) (α.hom.app (op k))).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel (α.hom.app (op k))
  have : (kernel (C := Y.Modules) (α.hom.app (op k))).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have : (cokernel (C := Y.Modules) (α.hom.app (op k))).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have : (((Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj.obj
        (op k)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hPAker : Stacks.Algebraization.IsPowerAnnihilated J
      (kernel (C := Y.Modules) (α.hom.app (op k))) :=
    ⟨k + 1, idealPowerMultiple_kernel_eq_bot J (k + 1) (α.hom.app (op k)) (G.property.2.1 k)⟩
  have hPAcok : Stacks.Algebraization.IsPowerAnnihilated J
      (cokernel (C := Y.Modules) (α.hom.app (op k))) :=
    ⟨k + 1, Stacks.Algebraization.idealPowerMultiple_eq_bot_of_epi J (k + 1)
      (cokernel.π (C := Y.Modules) (α.hom.app (op k)))
      (((Stacks.Algebraization.completionFunctor Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).property.2.1 k)⟩
  exact ⟨idealPowerMultiple_comap_ι_eq_bot_of_affine K t U _
      (fun _ hr a => smul_eq_zero_of_chart J K U t _ hPAker (hT k).1 hr a),
    idealPowerMultiple_comap_ι_eq_bot_of_affine K t U _
      (fun _ hr a => smul_eq_zero_of_chart J K U t _ hPAcok (hT k).2 hr a)⟩

end Stacks.Coherent

end
