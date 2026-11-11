module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry

/-!
# Algebraization of morphisms into a separated space locally of finite type (Stacks 0GHK)

Let `A` be a Noetherian ring complete with respect to an ideal `I`, `S = Spec A`, and let `X`,
`Y` be algebraic spaces over `S` with `X ⟶ S` proper and `Y ⟶ S` separated and only *locally*
of finite type. A compatible system of morphisms `g_n : X_n ⟶ Y_n` over the thickenings
`S_n = Spec (A / I^{n+1})` is the system of adic fibres of exactly one morphism `X ⟶ Y` over
`S`. This is the separated case of Remark 0GHK, which weakens the hypothesis "of finite type" on
`Y` in Stacks 0A4Z (`AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`).

The remark's reduction: the closed fibre `X_0` is quasi-compact, so the image of its points in
`|Y|` is quasi-compact and lies in a quasi-compact open `W ⊆ |Y|` (Stacks 04NN). Every `X_n` has
the same points as `X_0`, so every `X_n ⟶ Y` factors through the open subspace `V ⊆ Y` with
point set `W` (Stacks 03BZ). The open subspace `V` is separated and of finite type over `S`, so
Stacks 0A4Z applies to `V`. Uniqueness needs only separatedness of `Y`
(`AlgebraicGeometry.Space.eq_of_forall_adicFibreMap_eq`).

## Main results

* `AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_forall_isOpenSubspace`: the reduction to an
  open subspace of `Y` quasi-compact over `Spec A`.
* `AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_isLocallyOfFiniteType`: the existence
  half.
* `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType`: the separated
  case of Stacks 0GHK. The quasi-separated case is
  `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isQuasiSeparated`.

The index `n` stands for the source's `n + 1`: `X 0 = X_1`, `S 0 = S_1`.

## References

* [Stacks Project, Tag 0GHK](https://stacks.math.columbia.edu/tag/0GHK)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- In an algebraic space, every quasi-compact set of points lies in a quasi-compact open set of
points: cover it by finitely many quasi-compact open neighbourhoods (Stacks 04NN). -/
private theorem exists_isOpen_isCompact_superset {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {K : Set (points B S hS Y)} (hK : IsCompact K) :
    ∃ W : Set (points B S hS Y), IsOpen W ∧ IsCompact W ∧ K ⊆ W := by
  have hU : ∀ x : points B S hS Y, ∃ U : Set (points B S hS Y), IsOpen U ∧ IsCompact U ∧ x ∈ U :=
    fun x => by
      obtain ⟨U, hU, -⟩ :=
        (hasBasis_nhds_isOpen_isCompact B S hS Y hY x).mem_iff.mp Filter.univ_mem
      exact ⟨U, hU⟩
  choose U hUo hUc hxU using hU
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover U fun x _ => (hUo x).mem_nhds (hxU x)
  exact ⟨⋃ x ∈ t, U x, isOpen_biUnion fun x _ => hUo x, t.isCompact_biUnion fun x _ => hUc x,
    hKt⟩

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}
  {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}

/-- The transition map `X_n ⟶ X_{n+1}` between consecutive adic fibres of a presheaf over the
base is surjective on points: it is a base change of `Spec (A / I^{n+1}) ⟶ Spec (A / I^{n+2})`,
which is surjective. -/
theorem surjective_pointsMap_adicFibreSucc (fX : X ⟶ yoneda.obj (baseObject A B hS))
    (n : ℕ) :
    Function.Surjective (pointsMap B _ hS _ (adicFibreSucc A I B hS hSn fX n)) := by
  have hT : Function.Surjective (pointsMap B _ hS _
      (yoneda.map (adicThickeningSuccMap A I B hS hSn n))) :=
    (surjective_yonedaMap_iff_surjective_pointsMap B _ hS _).1
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ hS @Surjective _).2
        (surjective_adicThickeningSucc A I n))
  intro z
  obtain ⟨s, hs⟩ := hT (pointsMap B _ hS _
    (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn (n + 1)))) z)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B _ hS
    (isPullback_adicFibreSucc A I B hS hSn fX n) z s hs.symm
  exact ⟨w, hw⟩

section System

variable {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
  (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
  (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
    g n ≫ adicFibreSucc A I B hS hSn fY n)

include hgc in
/-- The composites `X_n ⟶ Y_n ⟶ Y` of a compatible system are compatible with the transition
maps of the adic fibres of `X`. -/
private theorem adicFibreSucc_comp_fst (n : ℕ) :
    adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) ≫
        pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))) =
      g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)) := by
  rw [reassoc_of% (hgc n), adicFibreSucc_fst]

include hgc in
/-- Every composite `X_n ⟶ Y_n ⟶ Y` of a compatible system has the same points in `|Y|` as the
one out of the closed fibre `X_0`, since `X_0 ⟶ X_n` is surjective on points. -/
private theorem range_pointsMap_comp_fst_subset (n : ℕ) :
    Set.range (pointsMap B _ hS _
        (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)))) ⊆
      Set.range (pointsMap B _ hS _
        (g 0 ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn 0)))) := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := surjective_pointsMap_adicFibreSucc fX n z
    refine ih ⟨w, ?_⟩
    rw [← adicFibreSucc_comp_fst g hgc n, pointsMap_comp]
    rfl

end System

include hSn in
/-- **The reduction of Stacks 0GHK to a quasi-compact target.** Let `A` be Noetherian and
`I`-adically complete, `X` proper and `Y` locally of finite type over `Spec A`, and let
`g_n : X_n ⟶ Y_n` be a compatible system over the thickenings. Suppose that for every open
subspace `V ⊆ Y` quasi-compact over `Spec A`, every compatible system `X_n ⟶ V_n` is the system
of adic fibres of a morphism `X ⟶ V`. Then `(g_n)` is the system of adic fibres of a morphism
`X ⟶ Y`.

The image in `|Y|` of the points of the quasi-compact closed fibre `X_0` lies in a quasi-compact
open `W`, and every `X_n ⟶ Y` factors through the open subspace `V` with points `W`, every
`X_n` having the same points as `X_0`. -/
theorem exists_adicFibreMap_eq_of_forall_isOpenSubspace [IsNoetherianRing A]
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n)
    (H : ∀ V : Subfunctor Y, IsOpenSubspace B _ hS V → IsQuasiCompact B _ hS (V.ι ≫ fY) →
      ∀ g' : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn (V.ι ≫ fY) n,
      (∀ n, g' n ≫ pullback.snd (V.ι ≫ fY) (yoneda.map (adicThickeningMap A I B hS hSn n)) =
        pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n))) →
      (∀ n, adicFibreSucc A I B hS hSn fX n ≫ g' (n + 1) =
        g' n ≫ adicFibreSucc A I B hS hSn (V.ι ≫ fY) n) →
      ∃ φ : X ⟶ V.toFunctor, ∃ hφ : φ ≫ V.ι ≫ fY = fX,
        ∀ n, adicFibreMap A I B hS hSn φ hφ n = g' n) :
    ∃ φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  have hSaff : IsAffine ((BigFppfOver.toScheme B _ hS).obj (baseObject A B hS)) := by
    change IsAffine (Spec (.of A))
    infer_instance
  -- The closed fibre `X_0` is quasi-compact.
  have hT0 : CompactSpace
      ((BigFppfOver.toScheme B _ hS).obj (adicThickeningObject A I B hS hSn 0)) := by
    change CompactSpace (adicThickening A I 0)
    infer_instance
  have hX0 : IsQuasiCompactSpace B _ hS (adicFibre A I B hS hSn fX 0) :=
    isQuasiCompactSpace_of_iso B _ hS (pullbackSymmetry _ _)
      (hpX.2.1.2 _ (isAlgebraicSpace_yoneda B _ hS _)
        (isQuasiCompact_yoneda_of_compact B _ hS _ hT0) _)
  have hX0c : CompactSpace (points B _ hS (adicFibre A I B hS hSn fX 0)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B _ hS _
      (isAlgebraicSpace_adicFibre A I B hS hSn hX fX 0)).1 hX0
  -- A quasi-compact open subspace `V ⊆ Y` containing the image of `X_0`.
  obtain ⟨W, hWo, hWc, hKW⟩ := exists_isOpen_isCompact_superset hY
    (isCompact_range (continuous_pointsMap B _ hS
      (g 0 ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn 0)))))
  set V := openSubspaceOfPoints B _ hS Y W with hVdef
  have hV : IsOpenSubspace B _ hS V := isOpenSubspace_openSubspaceOfPoints B _ hS hY W hWo
  have hVim : IsImmersion B _ hS V.ι := isImmersion_of_isOpenImmersion B _ hS hV.2
  have hVqc : IsQuasiCompactSpace B _ hS V.toFunctor := by
    rw [isQuasiCompactSpace_iff_compactSpace_points B _ hS _ hV.1]
    have hemb := isEmbedding_pointsMap_of_isImmersion B _ hS hY V.ι hVim
    refine ⟨hemb.isCompact_iff.mpr ?_⟩
    rw [Set.image_univ, range_pointsMap_ι_openSubspaceOfPoints]
    exact hWc
  have hqV : IsQuasiCompact B _ hS (V.ι ≫ fY) :=
    isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B _ hS (V.ι ≫ fY) hV.1 hbase
      fun T k hT => isQuasiCompact_yoneda_of_isAffine B _ hS k hT hSaff V.toFunctor hV.1 hVqc
        (V.ι ≫ fY)
  -- Every `X_n ⟶ Y` factors through `V`.
  have hle : ∀ n, Subfunctor.range
      (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n))) ≤ V := by
    intro n
    rintro T _ ⟨x, rfl⟩
    have hx : x ∈ (V.preimage
        (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)))).obj T := by
      rw [hVdef, preimage_openSubspaceOfPoints', mem_openSubspaceOfPoints_iff]
      rintro _ ⟨p, rfl⟩
      exact hKW (range_pointsMap_comp_fst_subset g hgc n ⟨_, rfl⟩)
    exact hx
  let h : ∀ n, adicFibre A I B hS hSn fX n ⟶ V.toFunctor := fun n => Subfunctor.lift _ (hle n)
  have hh : ∀ n, h n ≫ V.ι =
      g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
    fun n => Subfunctor.lift_ι _ _
  have hw : ∀ n, h n ≫ V.ι ≫ fY = pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫
      yoneda.map (adicThickeningMap A I B hS hSn n) := fun n => by
    rw [reassoc_of% (hh n), pullback.condition, reassoc_of% (hg n)]
  -- The induced compatible system into the adic fibres of `V`.
  let g' : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn (V.ι ≫ fY) n :=
    fun n => pullback.lift (h n) _ (hw n)
  have hg' : ∀ n, g' n ≫ pullback.snd (V.ι ≫ fY) (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
    fun n => pullback.lift_snd _ _ _
  have hgc' : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g' (n + 1) =
      g' n ≫ adicFibreSucc A I B hS hSn (V.ι ≫ fY) n := by
    intro n
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, adicFibreSucc_fst, pullback.lift_fst, pullback.lift_fst,
        ← cancel_mono V.ι, Category.assoc, hh, hh]
      exact adicFibreSucc_comp_fst g hgc n
    · rw [Category.assoc, Category.assoc, adicFibreSucc_snd, pullback.lift_snd, adicFibreSucc_snd,
        reassoc_of% (hg' n)]
  obtain ⟨φ, hφ, hφn⟩ := H V hV hqV g' hg' hgc'
  refine ⟨φ ≫ V.ι, (Category.assoc _ _ _).trans hφ, fun n => ?_⟩
  apply pullback.hom_ext
  · have h1 : h n = adicFibreMap A I B hS hSn φ hφ n ≫
        pullback.fst (V.ι ≫ fY) (yoneda.map (adicThickeningMap A I B hS hSn n)) := by
      rw [hφn n]
      exact (pullback.lift_fst _ _ _).symm
    rw [adicFibreMap_fst, ← hh n, h1, Category.assoc, adicFibreMap_fst_assoc]
  · rw [adicFibreMap_snd, hg n]

include hSn in
/-- **Stacks 0GHK, the separated case, existence.** Let `A` be Noetherian and `I`-adically
complete, `X` proper and `Y` separated and locally of finite type over `Spec A`. A compatible
system of morphisms `g_n : X_n ⟶ Y_n` over the thickenings is the system of adic fibres of a
morphism `X ⟶ Y`.

The image in `|Y|` of the points of the quasi-compact closed fibre `X_0` lies in a quasi-compact
open `W`, every `X_n ⟶ Y` factors through the open subspace `V` with points `W`
(`AlgebraicGeometry.Space.exists_adicFibreMap_eq_of_forall_isOpenSubspace`), and Stacks 0A4Z
applies to `V`, which is separated and of finite type over `Spec A`. -/
theorem exists_adicFibreMap_eq_of_isLocallyOfFiniteType [IsNoetherianRing A] [IsAdicComplete I A]
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX) (hsY : IsSeparated B _ hS fY)
    (hlY : IsLocallyOfFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃ φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  refine exists_adicFibreMap_eq_of_forall_isOpenSubspace hX hY hpX g hg hgc
    fun V hV hqV g' hg' hgc' => ?_
  have hVim : IsImmersion B _ hS V.ι := isImmersion_of_isOpenImmersion B _ hS hV.2
  -- `V` is separated and of finite type over the base.
  have hsV : IsSeparated B _ hS (V.ι ≫ fY) :=
    isSeparated_comp B _ hS _ _ (isSeparated_of_isImmersion B _ hS hVim) hsY
  have hfV : IsFiniteType B _ hS (V.ι ≫ fY) :=
    ⟨isLocallyOfFiniteType_comp' B _ hS V.ι fY hY hbase
      (isLocallyOfFiniteType_of_isImmersion B _ hS V.ι hVim) hlY, hqV⟩
  exact exists_adicFibreMap_eq g' hg' hX hV.1 hpX hsV hfV hgc'

/-- **Stacks 0GHK, the separated case.** Let `A` be a Noetherian ring complete with respect to
an ideal `I`, `S = Spec A`, `S_n = Spec (A / I^{n+1})`, and let `X`, `Y` be algebraic spaces over
`S` with `X ⟶ S` proper and `Y ⟶ S` separated and locally of finite type. A compatible system
of morphisms `g_n : X_n ⟶ Y_n` over the `S_n` between the adic fibres is the system of adic
fibres of exactly one morphism `g : X ⟶ Y` over `S`.

Remark 0GHK asks whether Stacks 0A4Z survives with `Y ⟶ S` only locally of finite type. This
declaration is the remark's assertion that the answer is yes when `Y ⟶ S` is separated, by the
remark's reduction to a quasi-compact open of `Y` containing the image of `g_1` (here `g 0`);
uniqueness is included, as in Stacks 0A4Z. The remark's further assertion for `Y ⟶ S`
quasi-separated is `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_of_isQuasiSeparated`,
and the two cases together are registered under Stacks 0GHK by
`AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq_separated_and_quasiSeparated`
(both in `StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraizationQuasiSeparated.lean`). -/
theorem existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType [IsNoetherianRing A]
    [IsAdicComplete I A] (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS))
    (hpX : IsProper B _ hS fX) (hsY : IsSeparated B _ hS fY)
    (hlY : IsLocallyOfFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃! φ : X ⟶ Y, ∃ hφ : φ ≫ fY = fX, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n := by
  obtain ⟨φ, hφ, hφn⟩ :=
    exists_adicFibreMap_eq_of_isLocallyOfFiniteType hX hY hpX hsY hlY g hg hgc
  refine ⟨φ, ⟨hφ, hφn⟩, fun φ' ⟨hφ', hφ'n⟩ => ?_⟩
  exact eq_of_forall_adicFibreMap_eq A I B hS hSn hX hY hpX hsY hφ' hφ fun n =>
    (hφ'n n).trans (hφn n).symm

end AlgebraicGeometry.Space

end
