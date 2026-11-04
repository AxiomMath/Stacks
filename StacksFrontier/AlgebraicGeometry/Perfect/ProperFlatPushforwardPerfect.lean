module

public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageDirected
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjectsDescent
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of the direct image along a flat proper morphism of finite presentation

Let `f : X ⟶ S` be a flat proper morphism of finite presentation and let `E` be a perfect object
of `D(𝒪_X)`. Then `Rf_*E` is a perfect object of `D(𝒪_S)`. This is the perfectness half of
clause (1) of [Stacks, Tag 0B91], over an **arbitrary** base `S`.

## The proof

The source's proof is the one of [Stacks, Tag 0A1H] at `𝒢^• = 𝒪_X`: Noetherian approximation.

1. Perfectness is local on `S`
   (`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`) and
   `(Rf_*E)|_V ≅ R(f|_V)_*(E|_{f⁻¹V})` ([Stacks, Tag 08FE]), so `S` may be taken affine.
2. For `S` affine, `S` is the limit of the Noetherian affine schemes `Spec ℤ[i]` for the finite
   subsets `i ⊆ Γ(S, 𝒪_S)` (`AlgebraicGeometry.affineStageCone`). By [Stacks, Tag 01ZM] part (1),
   [Stacks, Tag 01ZQ] and [Stacks, Tag 081F]
   (`AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`) and [Stacks, Tag 04AI]
   for flatness, `X ≅ X_i ×_{S_i} S` for a flat proper `X_i ⟶ S_i` of finite presentation:
   `exists_flat_isProper_finitePresentation_model_of_isAffine`.
3. The base changes `X_i ×_{S_i} S_k`, `k ≥ i`, form a situation of [Stacks, Tag 09RD] with limit
   `X` (`AlgebraicGeometry.directedBaseChangeDescentSituation`, re-pointed at `X`). Essential
   surjectivity in [Stacks, Tag 09RF] gives a stage `k` and a perfect `E_k` on `X_k` pulling back
   to `E`.
4. `X_k ⟶ S_k` is flat, proper and of finite presentation over the Noetherian `S_k`, so
   `R(f_k)_*E_k` is perfect ([Stacks, Tag 0B6G]); `X` and `S` are Tor independent over `S_k`,
   `f_k` being flat, so [Stacks, Tag 08IB] gives `Lπ_k^*R(f_k)_*E_k ≅ Rf_*E`, which is perfect by
   [Stacks, Tag 09UA].

## Main results

* `AlgebraicGeometry.exists_flat_isProper_finitePresentation_model_of_isAffine` — a flat proper
  morphism of finite presentation to an affine scheme is the base change of a flat proper morphism
  of finite presentation over a Noetherian stage of `affineStageCone`, isomorphism included.
* `AlgebraicGeometry.isPerfect_derivedPushforward_of_model` — `Rf_*E` is perfect when `f` is the
  base change of a flat proper morphism of finite presentation over a stage of a directed system of
  Noetherian schemes, along the projection from its limit.
* `AlgebraicGeometry.isPerfect_derivedPushforward_of_flat_of_isProper` — the perfectness half of
  [Stacks, Tag 0B91] (1), over an arbitrary base.
* `isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat_of_isProper`
  — **[Stacks, Tag 0B91] (1)**: perfectness together with the invertibility of the canonical base
  change map of [Stacks, Tag 08HY] for every cartesian square, by [Stacks, Tag 08IB].

## Implementation notes

The essential-surjectivity half of [Stacks, Tag 09RF] is
`AlgebraicGeometry.DescentSituation.exists_isPerfect_derivedPullback_iso`. It is applied to the
base-changed tower `AlgebraicGeometry.directedBaseChangeDescentSituation`, whose limit cone is
re-pointed at `X` itself along the isomorphism of the model, so that the descended object pulls
back to `E` on the nose and no transport along an isomorphism of schemes is needed afterwards.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### A flat proper model over a Noetherian stage -/

/-- **A flat proper morphism of finite presentation to an affine scheme comes from a Noetherian
stage.** Let `S` be affine and let `X` be flat, proper and of finite presentation over `S`. Then
for some finite subset `j` of `Γ(S, 𝒪_S)` there is a scheme `Xⱼ` flat, proper and of finite
presentation over `Spec ℤ[j]` with `X ≅ Xⱼ ×_{Spec ℤ[j]} S` over `S`.

The proper model is `AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`
([Stacks, Tag 01ZM] part (1), [Stacks, Tag 01ZQ], [Stacks, Tag 081F]); flatness descends to a later
stage by [Stacks, Tag 04AI], read at the structure morphism through
`AlgebraicGeometry.overPullback_map_terminal_iff`. -/
theorem exists_flat_isProper_finitePresentation_model_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (X : Over S) [IsProper X.hom] [Flat X.hom]
    (hX : FinitePresentation X.hom) :
    ∃ (j : (Finset Γ(S, ⊤))ᵒᵖ) (Xⱼ : Over ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj j)),
      FinitePresentation Xⱼ.hom ∧ IsProper Xⱼ.hom ∧ Flat Xⱼ.hom ∧
        Nonempty (X ≅ (Over.pullback ((affineStageCone S).π.app j)).obj Xⱼ) := by
  obtain ⟨i, Xᵢ, hfp, hprop, ⟨e⟩⟩ :=
    @exists_isProper_finitePresentation_model_of_isLimit _ _ _
      (specAdjoinFinsetDiagram Γ(S, ⊤)) _ _ _
      (affineStageCone S) (isLimit_affineStageCone S) X ‹IsProper X.hom› hX
  have : LocallyOfFinitePresentation Xᵢ.hom := hfp.1
  have : QuasiCompact Xᵢ.hom := hfp.2.1
  have : QuasiSeparated Xᵢ.hom := hfp.2.2
  have : CompactSpace Xᵢ.left := QuasiCompact.compactSpace_of_compactSpace Xᵢ.hom
  have : QuasiSeparatedSpace Xᵢ.left := quasiSeparatedSpace_of_quasiSeparated Xᵢ.hom
  have : IsProper Xᵢ.hom := hprop
  let f₀ : Xᵢ ⟶ Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj i)) := Over.homMk Xᵢ.hom
  have : LocallyOfFinitePresentation f₀.left := ‹LocallyOfFinitePresentation Xᵢ.hom›
  have : CompactSpace (Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj i))).left :=
    inferInstanceAs (CompactSpace ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace ((specAdjoinFinsetDiagram Γ(S, ⊤)).obj i))
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat ((Over.pullback ((affineStageCone S).π.app i)).map f₀).left :=
    (overPullback_map_terminal_iff @Flat ((affineStageCone S).π.app i) Xᵢ).2
      (prop_of_overIso @Flat e ‹Flat X.hom›)
  obtain ⟨k, a, hk⟩ := exists_flat_baseChange_of_limitBaseChange
    (specAdjoinFinsetDiagram Γ(S, ⊤)) (affineStageCone S) i Xᵢ _ f₀
    (isLimit_affineStageCone S)
  refine ⟨k, (Over.pullback ((specAdjoinFinsetDiagram Γ(S, ⊤)).map a)).obj Xᵢ,
    finitePresentation_overPullbackObj _ Xᵢ hfp, ?_,
    (overPullback_map_terminal_iff @Flat _ Xᵢ).1 hk,
    ⟨e ≪≫ overPullbackObj_shiftIso _ (affineStageCone S) a Xᵢ⟩⟩
  show IsProper (pullback.snd Xᵢ.hom ((specAdjoinFinsetDiagram Γ(S, ⊤)).map a))
  infer_instance

/-! ### The affine case -/

section Perfectness

/-- **The perfectness half of [Stacks, Tag 0B91] (1) through a Noetherian model.** Let `c` be a
limit cone of a directed system `D` of Noetherian schemes with affine transition morphisms, let
`w : P ⟶ D_i` be flat, proper and of finite presentation, and let `f : X ⟶ c.pt` be identified with
the base change of `w` along the projection `c.pt ⟶ D_i` by an isomorphism `φ : X ≅ c.pt ×_{D_i} P`
over `c.pt`. Then `Rf_*E` is perfect for every perfect `E` on `X`.

The base changes `D_k ×_{D_i} P` form a situation of [Stacks, Tag 09RD] with limit `X`, so `E`
descends to a perfect `E_k` at some stage ([Stacks, Tag 09RF], essential surjectivity);
[Stacks, Tag 0B6G] makes `R(f_k)_*E_k` perfect over the Noetherian `D_k`, [Stacks, Tag 08IB]
identifies its derived pullback to `c.pt` with `Rf_*E`, and [Stacks, Tag 09UA] makes that perfect.
-/
theorem isPerfect_derivedPushforward_of_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {a b : Iᵒᵖ} (e : a ⟶ b), IsAffineHom (D.map e)] [∀ a : Iᵒᵖ, IsNoetherian (D.obj a)]
    (c : Cone D) (hc : IsLimit c) (i : I) {P : Scheme.{u}} (w : P ⟶ D.obj (op i))
    [Flat w] [IsProper w] [LocallyOfFinitePresentation w]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (φ : X ≅ pullback (c.π.app (op i)) w)
    (hφ : φ.hom ≫ pullback.fst (c.π.app (op i)) w = f)
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    IsPerfect (X := c.pt.toRingedSpace) ((derivedPushforwardModules f).obj E) := by
  have hcpt : ∀ k : {k : I // i ≤ k},
      CompactSpace (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}) := fun k =>
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map (homOfLE k.2).op) w)
  have hqs : ∀ k : {k : I // i ≤ k},
      QuasiSeparatedSpace (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}) := fun k =>
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map (homOfLE k.2).op) w)
  let D₀ := directedBaseChangeDescentSituation D i w c hc hcpt hqs ⟨i, le_rfl⟩
  -- the tower, with its limit re-pointed at `X`
  let D₁ : DescentSituation.{u, u} {k : I // i ≤ k} :=
    { D₀ with
      limitCone := D₀.limitCone.extend φ.hom
      isLimit := IsLimit.ofIsoLimit D₀.isLimit (Cone.extendIso D₀.limitCone φ.symm) }
  obtain ⟨k, -, Ek, hEk, ⟨eE⟩⟩ := D₁.exists_isPerfect_derivedPullback_iso E
    ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace (X := X.toRingedSpace) E).1 hE)
  replace hEk : IsPerfect (X := (D₁.stage k).toRingedSpace) Ek :=
    (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace
      (X := (D₁.stage k).toRingedSpace) Ek).2 hEk
  -- the cartesian square at the stage `k`
  have hleg_fst : (directedBaseChangeCone D i w c).π.app (op k) ≫
      pullback.fst (D.map (homOfLE k.2).op) w =
      pullback.fst (c.π.app (op i)) w ≫ c.π.app (op k.1) :=
    directedBaseChangeCone_π_fst D i w c k
  have hleg_snd : (directedBaseChangeCone D i w c).π.app (op k) ≫
      pullback.snd (D.map (homOfLE k.2).op) w = pullback.snd (c.π.app (op i)) w :=
    directedBaseChangeCone_π_snd D i w c k
  have hbig : IsPullback (pullback.snd (c.π.app (op i)) w) (pullback.fst (c.π.app (op i)) w) w
      (c.π.app (op k.1) ≫ D.map (homOfLE k.2).op) := by
    rw [c.w]
    exact (IsPullback.of_hasPullback (c.π.app (op i)) w).flip
  rw [← hleg_snd] at hbig
  have hsq₀ : IsPullback ((directedBaseChangeCone D i w c).π.app (op k))
      (pullback.fst (c.π.app (op i)) w) (pullback.fst (D.map (homOfLE k.2).op) w)
      (c.π.app (op k.1)) :=
    IsPullback.of_right hbig hleg_fst (IsPullback.of_hasPullback (D.map (homOfLE k.2).op) w).flip
  have h₁ : IsPullback φ.hom f (pullback.fst (c.π.app (op i)) w) (𝟙 c.pt) :=
    IsPullback.of_horiz_isIso ⟨hφ.trans (Category.comp_id f).symm⟩
  have hsq' := h₁.paste_horiz hsq₀
  rw [Category.id_comp] at hsq'
  have hsq : IsPullback (D₁.projection k) f (pullback.fst (D.map (homOfLE k.2).op) w)
      (c.π.app (op k.1)) := hsq'
  -- the base change isomorphism of Tag 08IB
  have hTor : TorIndependent (pullback.fst (D.map (homOfLE k.2).op) w) (c.π.app (op k.1)) :=
    torIndependent_of_flat_left _ _
  have hqc := PerfectApproximation.isQuasicoherent_homology_of_isPerfect (D₁.stage k) Ek hEk
  have hiso := isIso_derivedBaseChangeMap_of_torIndependent
    (X := pullback (D.map (homOfLE k.2).op) w) hsq hTor Ek hqc
  -- perfectness at the Noetherian stage, Tag 0B6G, and Tag 09UA
  have hk : IsPerfect (X := (D.obj (op k.1)).toRingedSpace)
      ((derivedPushforwardModules (pullback.fst (D.map (homOfLE k.2).op) w)).obj Ek) :=
    Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect
      (X := pullback (D.map (homOfLE k.2).op) w) (pullback.fst (D.map (homOfLE k.2).op) w) Ek hEk
  have hpull := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (c.π.app (op k.1)).toLRSHom.toShHom _ hk
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
      f.toLRSHom.toShHom).mapIso eE)
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (@asIso _ _ _ _ _ hiso) hpull)

/-- **The perfectness half of [Stacks, Tag 0B91] (1) over an affine base.** The model is
`AlgebraicGeometry.exists_flat_isProper_finitePresentation_model_of_isAffine`, at which
`AlgebraicGeometry.isPerfect_derivedPushforward_of_model` applies. -/
theorem isPerfect_derivedPushforward_of_isAffine_of_flat_of_isProper
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E) := by
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  have : Flat (Over.mk f).hom := ‹Flat f›
  obtain ⟨⟨i⟩, Xj, hfpj, hpj, hflj, ⟨e⟩⟩ :=
    exists_flat_isProper_finitePresentation_model_of_isAffine S (Over.mk f)
      ⟨inferInstanceAs (LocallyOfFinitePresentation f), inferInstanceAs (QuasiCompact f),
        inferInstanceAs (QuasiSeparated f)⟩
  have : IsProper Xj.hom := hpj
  have : Flat Xj.hom := hflj
  have : LocallyOfFinitePresentation Xj.hom := hfpj.1
  exact isPerfect_derivedPushforward_of_model
    (specAdjoinFinsetDiagram Γ(S, ⊤)) (affineStageCone S) (isLimit_affineStageCone S) i Xj.hom
    (X := X) f
    ((Over.forget _).mapIso e ≪≫ pullbackSymmetry Xj.hom ((affineStageCone S).π.app (op i)))
    (by
      simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
      exact Over.w e.hom) E hE

/-- **The perfectness half of [Stacks, Tag 0B91] (1).** Let `f : X ⟶ S` be a flat proper morphism
of finite presentation and let `E` be a perfect object of `D(𝒪_X)`. Then `Rf_*E` is a perfect
object of `D(𝒪_S)`.

Perfectness is local on `S`, and over an affine open `V ⊆ S` the restriction of `Rf_*E` is
`R(f|_V)_*(E|_{f⁻¹V})` ([Stacks, Tag 08FE]), which is perfect by the affine case. -/
theorem isPerfect_derivedPushforward_of_flat_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E) := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect
    (X := S.toRingedSpace) _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  refine ⟨V, hxV, ?_⟩
  have : IsAffine (V : S.Opens).toScheme := hV
  have hE' : IsPerfect (X := (f ⁻¹ᵁ V).toScheme.toRingedSpace)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).mapDerivedCategory.obj E) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (f ⁻¹ᵁ V).toScheme.toRingedSpace)
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback (f ⁻¹ᵁ V).ι).app E).symm
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
        (f ⁻¹ᵁ V).ι.toLRSHom.toShHom E hE)
  have hV' := isPerfect_derivedPushforward_of_isAffine_of_flat_of_isProper
    (f ∣_ V) _ hE'
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := S.toRingedSpace.restrict V.isOpenEmbedding)
    (((RingedSpace.derivedRestrictModulesIsoRestrictFunctor S V).app _ ≪≫
      schemeDerivedPushforwardRestrictOpensIso f V E).symm) hV'

/-- **[Stacks, Tag 0B91] (1).** Let `f : X ⟶ S` be a flat proper morphism of finite presentation
and let `E` be a perfect object of `D(𝒪_X)`. Then `Rf_*E` is a perfect object of `D(𝒪_S)`, and its
formation commutes with arbitrary base change: for every cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
the canonical base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an
isomorphism.

Perfectness is `isPerfect_derivedPushforward_of_flat_of_isProper`. For base change, `f` is flat, so
`X` and `S'` are Tor independent over `S`, and `E` has quasi-coherent cohomology, so the canonical
map is invertible by [Stacks, Tag 08IB]. -/
@[stacks 0B91 "clause (1) in full: perfectness of Rf_*E, and invertibility of the canonical base \
change map Lg^*Rf_*E --> Rf'_*L(g')^*E of Tag 08HY for every cartesian square, which is what 'its \
formation commutes with arbitrary base change' means; finite presentation of the \
proper f is spelled LocallyOfFinitePresentation, the quasi-compactness and quasi-separation it adds \
being part of properness",
  sga "6 IV 3.1.1" "special case"]
theorem isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    IsPerfect (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E) ∧
      ∀ {S' X' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
          (comp_toShHom_of_comm sq.w) E) :=
  ⟨isPerfect_derivedPushforward_of_flat_of_isProper f E hE, fun g _ _ sq =>
    isIso_derivedBaseChangeMap_of_torIndependent sq (torIndependent_of_flat_left f g) E
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect X E hE)⟩

end Perfectness

end AlgebraicGeometry

end
