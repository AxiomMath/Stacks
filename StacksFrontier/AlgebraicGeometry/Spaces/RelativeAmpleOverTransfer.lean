module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

/-!
# Ampleness over a subfunctor: transfer along base change and to opens of the scheme

`AlgebraicGeometry.Space.IsRelativelyAmpleOver f L W` says that the pullback of `L` is ample on
every base change of `f : X ⟶ Y` along a morphism factoring through the subfunctor `W` of `Y`.
This file records three formal properties used to assemble the proof of Stacks 0D3A:

* it is antitone in `W`;
* ampleness over `W ⊆ Y'` for a base change `f' : X' ⟶ Y'` of `f` along a monomorphism
  `Y' ⟶ Y` gives ampleness of `f` over the image of `W` in `Y`;
* for `Y` a scheme, an open subspace `W` of `h_Y` contains the open subspace cut out by an open
  of the scheme around each of its points, and ampleness over the latter is ampleness on every
  base change along `openSub Y V ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.IsRelativelyAmpleOver.mono`
* `AlgebraicGeometry.Space.isRelativelyAmpleOver_range_of_isPullback`
* `AlgebraicGeometry.Space.exists_mem_range_openSubHom_le`
* `AlgebraicGeometry.Space.IsRelativelyAmpleOver.isRelativelyAmple_openSub`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Ampleness over a subfunctor is inherited by smaller subfunctors.** -/
theorem IsRelativelyAmpleOver.mono {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} {W W' : Subfunctor Y.1}
    (h : IsRelativelyAmpleOver f L W) (hW : W' ≤ W) : IsRelativelyAmpleOver f L W' := by
  rintro X' Y' g p f' hsq ⟨l, hl⟩
  exact h g p f' hsq ⟨l ≫ Subfunctor.homOfLe hW, by rw [Category.assoc, Subfunctor.homOfLe_ι, hl]⟩

/-- **Ampleness over a subfunctor of the target of a base change along a monomorphism is ampleness
of the original morphism over its image.**  If `f' : X' ⟶ Y'` is the base change of `f : X ⟶ Y`
along a monomorphism `ι : Y' ⟶ Y` and the pullback of `L` to `X'` is ample over `W ⊆ Y'`, then
`L` is ample over the image of `W` in `Y`. -/
theorem isRelativelyAmpleOver_range_of_isPullback {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {ι : Y' ⟶ Y} [Mono ι.hom] {p' : X' ⟶ X} {f' : X' ⟶ Y'}
    (hsq' : IsPullback p' f' f ι) (L : Modules.{u, u} B S hS X.1 X.2) {W : Subfunctor Y'.1}
    (h : IsRelativelyAmpleOver f' ((modulePullback B S hS p').obj L) W) :
    IsRelativelyAmpleOver f L (Subfunctor.range (W.ι ≫ ι.hom)) := by
  rintro X'' Y'' g p f'' hsq ⟨l, hl⟩
  let l' : Y''.1 ⟶ W.toFunctor := l ≫ inv (Subfunctor.toRange (W.ι ≫ ι.hom))
  have hl' : l' ≫ W.ι ≫ ι.hom = g.hom := by
    have hι : inv (Subfunctor.toRange (W.ι ≫ ι.hom)) ≫ W.ι ≫ ι.hom =
        (Subfunctor.range (W.ι ≫ ι.hom)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm
    rwa [Category.assoc, hι]
  let gV : Y'' ⟶ Y' := ObjectProperty.homMk (l' ≫ W.ι)
  have hgV : gV ≫ ι = g := by
    ext1
    change (l' ≫ W.ι) ≫ ι.hom = g.hom
    rwa [Category.assoc]
  let pc : X'' ⟶ X' := hsq'.lift p (f'' ≫ gV) (by rw [Category.assoc, hgV]; exact hsq.w)
  have hpc : pc ≫ p' = p := hsq'.lift_fst _ _ _
  have hsqc : IsPullback pc f'' f' gV :=
    IsPullback.of_right (by rw [hpc, hgV]; exact hsq) (hsq'.lift_snd _ _ _) hsq'
  rw [← hpc]
  exact (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS pc p').app L)).mp
    (h gV pc f'' hsqc ⟨l', rfl⟩)

/-- **An open subspace of a scheme contains the open subspace cut out by an open of the scheme
around each of its points.**  The open is the set of points of the scheme lying in the open
subspace, read through Stacks 03BX. -/
theorem exists_mem_range_openSubHom_le {Y : BigFppfOver B S hS} {W : Subfunctor (yoneda.obj Y)}
    (hW : IsOpenSubspace B S hS W) (y : (BigFppfOver.toScheme B S hS).obj Y)
    (hy : (schemePointsHomeomorph B S hS Y).symm y ∈
      Set.range (pointsMap B S hS W.toFunctor W.ι)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      Subfunctor.range (yoneda.map (openSubHom Y V)) ≤ W := by
  let V : ((BigFppfOver.toScheme B S hS).obj Y).Opens :=
    ⟨(schemePointsHomeomorph B S hS Y).symm ⁻¹' Set.range (pointsMap B S hS W.toFunctor W.ι),
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2).preimage
        (schemePointsHomeomorph B S hS Y).symm.continuous⟩
  have _ : Mono (yoneda.map (openSubHom Y V)) :=
    mono_of_presheaf_isOpenImmersion (isOpenImmersion_yoneda_map_openSubHom Y V)
  refine ⟨V, hy, le_of_range_pointsMap_ι_subset B S hS hW ?_⟩
  rintro _ ⟨w, rfl⟩
  have hw : pointsMap B S hS _ (Subfunctor.range (yoneda.map (openSubHom Y V))).ι w ∈
      Set.range (pointsMap B S hS (yoneda.obj (openSub Y V)) (yoneda.map (openSubHom Y V))) := by
    obtain ⟨w', rfl⟩ := pointsMap_surjective_of_isIso B S hS
      (Subfunctor.toRange (yoneda.map (openSubHom Y V))) w
    exact ⟨w', by rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
  rw [range_pointsMap_yoneda_map_openSubHom] at hw
  rwa [← (schemePointsHomeomorph B S hS Y).symm_apply_apply
    (pointsMap B S hS _ (Subfunctor.range (yoneda.map (openSubHom Y V))).ι w)]

/-- **Ampleness over the open subspace cut out by an open of the scheme is ampleness on every
base change along `openSub Y V ⟶ Y`.** -/
theorem IsRelativelyAmpleOver.isRelativelyAmple_openSub {X : AlgebraicSpaces B S hS}
    {Y : BigFppfOver B S hS} {f : X ⟶ schemeSpace Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (V : ((BigFppfOver.toScheme B S hS).obj Y).Opens)
    (h : IsRelativelyAmpleOver f L (Subfunctor.range (yoneda.map (openSubHom Y V))))
    ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
    (f₁ : X₁ ⟶ schemeSpace (openSub Y V))
    (hsq₁ : IsPullback p₁ f₁ f (ObjectProperty.homMk (yoneda.map (openSubHom Y V)))) :
    IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) :=
  h _ p₁ f₁ hsq₁ ⟨Subfunctor.toRange (yoneda.map (openSubHom Y V)),
    Subfunctor.toRange_ι _⟩

end AlgebraicGeometry.Space

end
