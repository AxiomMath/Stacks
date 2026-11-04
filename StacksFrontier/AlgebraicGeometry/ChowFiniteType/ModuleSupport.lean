module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic

/-!
# Descending properness, and properness of the support of a module, to a finite stage

Let `S = lim S_i` be the limit of a cofiltered inverse system of schemes with affine transition
morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated schemes over a
quasi-compact quasi-separated stage `S₀`, and write `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` for the
base changes of `f₀` to `S_i` and to `S`. This is Situation 081D.

**Stacks 081F** says that if `f₀` is locally of finite type and `f` is proper, then `f_i` is
proper for some `i`. **Stacks 081G** is its module version: if moreover `F₀` is a quasi-coherent
`O_{X₀}`-module of finite type, with pullbacks `F_i` and `F` to `X_i` and to `X`, and the
scheme-theoretic support of `F` is proper over `Y`, then the scheme-theoretic support of `F_i`
is proper over `Y_i` for some `i`.

## Main results

* `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit`: Stacks 081F.
* `AlgebraicGeometry.exists_isProper_schemeTheoreticSupport_baseChange_of_isLimit`: Stacks 081G.

## Implementation notes

Stacks 081F already exists in this repository in two conditional forms —
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_hasChowModification`, on the
hypothesis of Chow's lemma for `f₀`, and
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep`, which
discharges that hypothesis from
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep` but asks in exchange that
`f₀` be separated, because Chow's lemma does. The tag was withheld there for that reason. Here
the separatedness hypothesis is removed the way the Stacks proof removes it: Stacks 01ZQ,
`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`, makes the base change of `f₀`
separated at some stage `i₁`, the whole situation is re-indexed at `i₁`, and the conclusion is
carried back along the composite transition `i ⟶ i₁ ⟶ i₀`. Both moves are
`AlgebraicGeometry.overPullback_map_comp_iff` together with `CategoryTheory.Limits.Cone.w` and
`CategoryTheory.Functor.map_comp`, exactly as in the proof of
`AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit`; the re-indexed stage is
quasi-compact and quasi-separated because the transition morphisms, and hence their base
changes, are affine.

For Stacks 081G the Stacks proof replaces `X₀` by the scheme-theoretic support of `F₀`. That
replacement is carried out here by applying Stacks 081F to the morphism `Z₀ ⟶ Y₀` out of the
closed subscheme `Z₀` cut out by
`AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F₀`, regarded as a scheme over `S₀`.
Properness of the support is moved across the replacement in both directions by
`AlgebraicGeometry.exists_isProper_iff_forall_isProper`: the base change of `Z₀` to a stage is
the closed subscheme of `X_i` cut out by the inverse image ideal sheaf, which is a *different*
closed subscheme structure from the scheme-theoretic support of `F_i` — the annihilator of a
finite module does not commute with non-flat base change — but it cuts out the *same* closed
subset, since the support of a pullback is the inverse image of the support
(`SheafOfModules.supp_pullback`, Stacks 056J) and the support of an inverse image ideal sheaf is
the inverse image of its support (`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`), and
properness over the base depends only on the closed subset. This is the content of the Stacks
proof's appeal to the universal homeomorphism `Z → X`.

The identification of the base change of `Z₀` with that closed subscheme of `X_i` is the
composite of `AlgebraicGeometry.Scheme.IdealSheafData.comapIso` with the symmetry and pasting
isomorphisms for fibre products; `comapPullbackIso_hom_comp` records that it is compatible with
the two morphisms to the base change of `Y₀`.

No smallness condition is part of Situation 081D, but `CategoryTheory.EssentiallySmall.{u} I`
is a genuine hypothesis of this family of lemmas and is inherited from Stacks 01ZP and 01ZQ; see
the implementation notes of `AlgebraicGeometry.MorphismDescentSituation`. The inverse system is
a cofiltered category rather than a directed partially ordered set, and "some `i ≥ 0`" is an
object `i` together with a morphism `i ⟶ i₀`, as in the rest of this family.

## References

* [Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 081G](https://stacks.math.columbia.edu/tag/081G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-- Any two closed subscheme structures on the same closed subset of `X` are simultaneously
proper over the base. -/
@[ega "II 5.4.10" "more general"]
private theorem isProper_subschemeι_of_support_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (I J : X.IdealSheafData) (h : I.support = J.support)
    (hI : IsProper (I.subschemeι ≫ f)) : IsProper (J.subschemeι ≫ f) :=
  (exists_isProper_iff_forall_isProper f I.support).1 ⟨I, rfl, hI⟩ J h.symm

section Support

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- The scheme-theoretic support of a pullback and the inverse image of the scheme-theoretic
support are two closed subscheme structures on the same closed subset. -/
private theorem support_schemeTheoreticSupport_pullback :
    (Scheme.Modules.schemeTheoreticSupport ((Scheme.Modules.pullback p).obj F)).support =
      ((Scheme.Modules.schemeTheoreticSupport F).comap p).support := by
  refine Closeds.ext ?_
  rw [← Scheme.Modules.supp_eq_support_schemeTheoreticSupport,
    SheafOfModules.supp_pullback, Scheme.IdealSheafData.support_comap,
    Scheme.Modules.supp_eq_support_schemeTheoreticSupport]
  rfl

end Support

section Bridge

variable {S T : Scheme.{u}} (p : T ⟶ S) {X₀ Y₀ : Over S} (f₀ : X₀ ⟶ Y₀)
  (I : X₀.left.IdealSheafData)

/-- A closed subscheme of `X₀`, viewed as a scheme over `S`. -/
private noncomputable abbrev closedOver : Over S := Over.mk (I.subschemeι ≫ X₀.hom)

/-- The restriction of `f₀` to a closed subscheme of its source, as a morphism over `S`. -/
private noncomputable abbrev closedHom : closedOver I ⟶ Y₀ :=
  Over.homMk (I.subschemeι ≫ f₀.left) (by
    change (I.subschemeι ≫ f₀.left) ≫ Y₀.hom = I.subschemeι ≫ X₀.hom
    rw [Category.assoc, Over.w f₀])

/-- The base change along `p` of a closed subscheme of `X₀` is the closed subscheme of the base
change of `X₀` cut out by the inverse image ideal sheaf. -/
private noncomputable def comapPullbackIso :
    (I.comap (pullback.fst X₀.hom p)).subscheme ≅ ((Over.pullback p).obj (closedOver I)).left :=
  I.comapIso (pullback.fst X₀.hom p) ≪≫
    pullbackSymmetry (pullback.fst X₀.hom p) I.subschemeι ≪≫
    pullbackRightPullbackFstIso X₀.hom p I.subschemeι

/-- The identification of the base change of a closed subscheme of `X₀` with a closed subscheme
of the base change of `X₀` is compatible with the two morphisms to the base change of `Y₀`. -/
private theorem comapPullbackIso_hom_comp :
    (comapPullbackIso p I).hom ≫ ((Over.pullback p).map (closedHom f₀ I)).left =
      (I.comap (pullback.fst X₀.hom p)).subschemeι ≫ ((Over.pullback p).map f₀).left := by
  have hfst : (comapPullbackIso p I).hom ≫
      pullback.fst (I.subschemeι ≫ X₀.hom) p ≫ I.subschemeι =
        (I.comap (pullback.fst X₀.hom p)).subschemeι ≫ pullback.fst X₀.hom p := by
    rw [comapPullbackIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
      pullbackRightPullbackFstIso_hom_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc,
      ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  have hsnd : (comapPullbackIso p I).hom ≫ pullback.snd (I.subschemeι ≫ X₀.hom) p =
      (I.comap (pullback.fst X₀.hom p)).subschemeι ≫ pullback.snd X₀.hom p := by
    rw [comapPullbackIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
      pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  apply pullback.hom_ext
  · rw [Category.assoc, overPullback_map_left_fst, Category.assoc, overPullback_map_left_fst]
    show (comapPullbackIso p I).hom ≫
        pullback.fst (I.subschemeι ≫ X₀.hom) p ≫ I.subschemeι ≫ f₀.left = _
    rw [← Category.assoc (pullback.fst (I.subschemeι ≫ X₀.hom) p), ← Category.assoc, hfst,
      Category.assoc]
  · rw [Category.assoc, overPullback_map_left_snd, Category.assoc, overPullback_map_left_snd]
    exact hsnd

/-- Properness over the base change of `Y₀` of the base change of the scheme-theoretic support
of `F₀` is properness of the scheme-theoretic support of the base change of `F₀`: the two are
closed subscheme structures on the same closed subset. -/
private theorem isProper_overPullback_closedHom_iff
    (F₀ : X₀.left.Modules) [F₀.IsQuasicoherent] [F₀.IsFiniteType]
    [LocallyOfFiniteType f₀.left] :
    IsProper ((Over.pullback p).map
        (closedHom f₀ (Scheme.Modules.schemeTheoreticSupport F₀))).left ↔
      IsProper ((Scheme.Modules.schemeTheoreticSupport
          ((Scheme.Modules.pullback (pullback.fst X₀.hom p)).obj F₀)).subschemeι ≫
          ((Over.pullback p).map f₀).left) := by
  have : LocallyOfFiniteType ((Over.pullback p).map f₀).left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) p f₀ inferInstance
  have hsupp := support_schemeTheoreticSupport_pullback (pullback.fst X₀.hom p) F₀
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    (comapPullbackIso p (Scheme.Modules.schemeTheoreticSupport F₀)).hom _,
    comapPullbackIso_hom_comp]
  exact ⟨isProper_subschemeι_of_support_eq _ _ _ hsupp.symm,
    isProper_subschemeι_of_support_eq _ _ _ hsupp⟩

end Bridge

section Descent

variable {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  (c : Cone D) (i₀ : I)

/-- **Stacks 081F.** Assumptions and notation as in Situation 081D: `D` is a cofiltered inverse
system of schemes with affine transition morphisms and limit cone `c`, and `f₀ : X₀ ⟶ Y₀` is a
morphism of quasi-compact quasi-separated schemes over the quasi-compact quasi-separated stage
`D.obj i₀`. If `f₀` is locally of finite type and its base change to the limit is proper, then
its base change to some later stage is proper.

Chow's lemma over the quasi-compact quasi-separated `Y₀` needs `f₀` to be separated, which is
not assumed; following the Stacks proof, Stacks 01ZQ supplies separatedness at some stage `i₁`
and the situation is re-indexed there before
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep` is applied. -/
@[stacks 081F]
theorem exists_isProper_baseChange_of_isLimit
    (hc : IsLimit c) (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsProper ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Over.pullback (D.map hi)).map f₀).left := by
  obtain ⟨i₁, h₁, hsep₁⟩ := exists_isSeparated_baseChange_of_isLimit D c i₀ X₀ Y₀ f₀ hc
  let X₁ := (Over.pullback (D.map h₁)).obj X₀
  let Y₁ := (Over.pullback (D.map h₁)).obj Y₀
  let f₁ : X₁ ⟶ Y₁ := (Over.pullback (D.map h₁)).map f₀
  have : IsSeparated f₁.left := hsep₁
  have : CompactSpace (D.obj i₁) :=
    QuasiCompact.compactSpace_of_compactSpace (D.map h₁)
  have : QuasiSeparatedSpace (D.obj i₁) :=
    quasiSeparatedSpace_of_quasiSeparated (D.map h₁)
  have : CompactSpace X₁.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst X₀.hom (D.map h₁))
  have : QuasiSeparatedSpace X₁.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst X₀.hom (D.map h₁))
  have : CompactSpace Y₁.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst Y₀.hom (D.map h₁))
  have : QuasiSeparatedSpace Y₁.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst Y₀.hom (D.map h₁))
  have : LocallyOfFiniteType f₁.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) (D.map h₁) f₀ inferInstance
  have : IsProper ((Over.pullback (c.π.app i₁)).map f₁).left := by
    apply (overPullback_map_comp_iff (@IsProper) (D.map h₁) (c.π.app i₁) f₀).mp
    rw [c.w h₁]
    infer_instance
  obtain ⟨i, h, hp⟩ := exists_isProper_baseChange_of_isLimit_of_isOneAffineOpenStep
    Scheme.FiniteTypeApproximation.isOneAffineOpenStep D c hc i₁ X₁ Y₁ f₁
  refine ⟨i, h ≫ h₁, ?_⟩
  rw [D.map_comp]
  exact (overPullback_map_comp_iff (@IsProper) (D.map h₁) (D.map h) f₀).mpr hp

/-- **Stacks 081G.** Assumptions and notation as in Situation 081D, and let `F₀` be a
quasi-coherent `O_{X₀}`-module, with `F` and `F_i` its pullbacks to the base changes `X` and
`X_i` of `X₀`. Assume `f₀` is locally of finite type, `F₀` is of finite type, and the
scheme-theoretic support of `F` is proper over `Y`. Then the scheme-theoretic support of `F_i`
is proper over `Y_i` for some `i`.

The base change of `X₀` to a stage is the fibre product of `X₀.hom` with the transition
morphism, so the pullback of `F₀` to it is its pullback along
`CategoryTheory.Limits.pullback.fst`. The proof applies Stacks 081F to the restriction of `f₀`
to the scheme-theoretic support of `F₀`. -/
@[stacks 081G]
theorem exists_isProper_schemeTheoreticSupport_baseChange_of_isLimit
    (hc : IsLimit c) (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) (F₀ : X₀.left.Modules)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left] [F₀.IsQuasicoherent] [F₀.IsFiniteType]
    (hlim : IsProper ((Scheme.Modules.schemeTheoreticSupport
        ((Scheme.Modules.pullback (pullback.fst X₀.hom (c.π.app i₀))).obj F₀)).subschemeι ≫
        ((Over.pullback (c.π.app i₀)).map f₀).left)) :
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Scheme.Modules.schemeTheoreticSupport
        ((Scheme.Modules.pullback (pullback.fst X₀.hom (D.map hi))).obj F₀)).subschemeι ≫
        ((Over.pullback (D.map hi)).map f₀).left) := by
  have : CompactSpace (closedOver (Scheme.Modules.schemeTheoreticSupport F₀)).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (Scheme.Modules.schemeTheoreticSupport F₀).subschemeι
  have : QuasiSeparatedSpace (closedOver (Scheme.Modules.schemeTheoreticSupport F₀)).left :=
    quasiSeparatedSpace_of_quasiSeparated
      (Scheme.Modules.schemeTheoreticSupport F₀).subschemeι
  have : LocallyOfFiniteType
      (closedHom f₀ (Scheme.Modules.schemeTheoreticSupport F₀)).left := by
    show LocallyOfFiniteType
      ((Scheme.Modules.schemeTheoreticSupport F₀).subschemeι ≫ f₀.left)
    infer_instance
  have : IsProper ((Over.pullback (c.π.app i₀)).map
      (closedHom f₀ (Scheme.Modules.schemeTheoreticSupport F₀))).left :=
    (isProper_overPullback_closedHom_iff (c.π.app i₀) f₀ F₀).mpr hlim
  obtain ⟨i, hi, hp⟩ := exists_isProper_baseChange_of_isLimit D c i₀ hc
    (closedOver (Scheme.Modules.schemeTheoreticSupport F₀)) Y₀
    (closedHom f₀ (Scheme.Modules.schemeTheoreticSupport F₀))
  exact ⟨i, hi, (isProper_overPullback_closedHom_iff (D.map hi) f₀ F₀).mp hp⟩

end Descent

end AlgebraicGeometry

end
