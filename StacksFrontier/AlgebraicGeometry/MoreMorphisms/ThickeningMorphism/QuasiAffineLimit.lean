module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemLimit
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.QuasiAffineAscent

/-!
# The ascent of quasi-affineness along an arbitrary thickening, by the limit argument

Let `k : Y ⟶ Y'` be a thickening — a closed immersion surjective on points — with `Y`
quasi-affine. Then `Y'` is quasi-affine, with no Noetherian hypothesis.

`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean` proves
this when some power of the kernel ideal sheaf of `k` vanishes, by an elementary Čech
computation, hence whenever `Y'` is locally Noetherian. This file removes that hypothesis by the
limit argument the source uses for [Stacks Project, Tag 09MW], of which the statement proved here
is the case `L = 𝒪` read through [Stacks Project, Tag 01QE].

## The argument

`Y'` is quasi-compact and quasi-separated, being homeomorphic to the quasi-affine `Y`, so
absolute Noetherian approximation
(`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType`,
[Stacks Project, Tag 01ZA]) writes `Y' = lim Xᵢ` over a directed set, with affine transition
morphisms and every `Xᵢ` of finite type over the integers, hence Noetherian.

Let `Zᵢ ⊆ Xᵢ` be the scheme-theoretic image of `Y`, that is the closed subscheme cut out by the
image of the kernel ideal sheaf of `k` under the projection. Then `Y = lim Zᵢ`
(`Stacks.Thickenings.imageSubschemeConeIsLimit`), because the kernel ideal sheaf is the supremum
of the inverse images of its images (`AlgebraicGeometry.le_iSup_comap_map_of_isLimit`). The `Zᵢ`
are Noetherian, being closed subschemes of the `Xᵢ`, and the transition morphisms of that system
are affine.

Quasi-affineness descends to a stage: `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit`
([Stacks Project, Tag 01Z5]) gives one `i` with `Zᵢ` quasi-affine. The support of the ideal sheaf
of `Zᵢ` is closed in the Noetherian space `Xᵢ`, hence constructible, and it contains the image of
`Y'`, because it contains the image of `Y` and `k` is surjective; so by [Stacks Project, Tag 05F4]
(`AlgebraicGeometry.eventually_range_transition_subset_of_isLocallyConstructible`) there is a
later stage `l` whose transition morphism `g : X_l ⟶ Xᵢ` already lands in `Zᵢ`
set-theoretically.

Let `T = X_l ×_{Xᵢ} Zᵢ`. Its projection to `Zᵢ` is affine, so `T` is quasi-affine; its projection
to `X_l` is a closed immersion, surjective because `g` lands in `Zᵢ`, hence a thickening of the
**Noetherian** scheme `X_l`. The finite-order case
`Stacks.Thickenings.isQuasiAffine_of_isThickening_of_isLocallyNoetherian` therefore applies and
makes `X_l` quasi-affine; and `Y' ⟶ X_l` is affine, so `Y'` is quasi-affine.

## Main results

* `Stacks.Thickenings.imageSubschemeConeIsLimit`: a closed subscheme of the limit of a system
  with affine transition morphisms is the limit of its scheme-theoretic images in the stages.
* `Stacks.Thickenings.isQuasiAffine_of_isThickening_of_descentSituation`: the ascent of
  quasi-affineness along a thickening of the limit of a directed system of Noetherian schemes
  with affine transition morphisms.
* `Stacks.Thickenings.isQuasiAffine_of_isThickening`: **the ascent of quasi-affineness along an
  arbitrary thickening**, with no hypothesis beyond the source's.
* `Stacks.Thickenings.quasiAffineAscendsAlongThickening`:
  `Stacks.Thickenings.QuasiAffineAscendsAlongThickening` discharged.
* `Stacks.Thickenings.isQuasiAffine_iff_of_isThickening`: **[Stacks Project, Tag 0B7L]**, both
  implications, with no hypothesis beyond the source's.
* `Stacks.Thickenings.isQuasiAffineHom_left_iff_right`: **part (9) of
  [Stacks Project, Tag 09ZV]**, with no hypothesis beyond the source's.

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
* [Stacks Project, Tag 0B7L](https://stacks.math.columbia.edu/tag/0B7L)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01Z5](https://stacks.math.columbia.edu/tag/01Z5)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter Opposite

namespace Stacks.Thickenings

universe u

/-! ### The scheme-theoretic images of a closed subscheme in the stages of a limit -/

/-- The inverse system of the closed subschemes of the stages cut out by the images of an ideal
sheaf of the limit — the scheme-theoretic images of the closed subscheme it defines. -/
@[reducible] noncomputable def imageSubschemeDiagram {J : Type u} [Category.{u} J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (I : c.pt.IdealSheafData) : J ⥤ Scheme.{u} where
  obj j := (I.map (c.π.app j)).subscheme
  map {j k} f :=
    Scheme.IdealSheafData.subschemeMap (I.map (c.π.app j)) (I.map (c.π.app k))
      (D.map f) (by rw [← Scheme.IdealSheafData.map_comp, c.w f])
  map_id j := by
    apply (cancel_mono (I.map (c.π.app j)).subschemeι).1
    simp [Scheme.IdealSheafData.subschemeMap_subschemeι]
  map_comp f g := by
    apply (cancel_mono (I.map (c.π.app _)).subschemeι).1
    simp [Scheme.IdealSheafData.subschemeMap_subschemeι, Category.assoc]

/-- The inclusions of the scheme-theoretic images into the stages, as a natural transformation. -/
@[reducible] noncomputable def imageSubschemeInclusion {J : Type u} [Category.{u} J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (I : c.pt.IdealSheafData) :
    imageSubschemeDiagram D c I ⟶ D where
  app j := (I.map (c.π.app j)).subschemeι
  naturality f := by
    simp [imageSubschemeDiagram, Scheme.IdealSheafData.subschemeMap_subschemeι]

/-- The cone on `Stacks.Thickenings.imageSubschemeDiagram` with the closed subscheme of the limit
as its vertex: a closed subscheme maps to its scheme-theoretic image in every stage. -/
@[reducible] noncomputable def imageSubschemeCone {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    (c : Cone D) {Z : Scheme.{u}} (i : Z ⟶ c.pt) [IsClosedImmersion i] :
    Cone (imageSubschemeDiagram D c i.ker) where
  pt := Z
  π :=
    { app j :=
        (IsClosedImmersion.lift (i.ker.map (c.π.app j)).subschemeι (i ≫ c.π.app j)
          (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp]) :
            Z ⟶ (i.ker.map (c.π.app j)).subscheme)
      naturality := by
        intro j k f
        apply (cancel_mono (i.ker.map (c.π.app k)).subschemeι).1
        simp [imageSubschemeDiagram, Scheme.IdealSheafData.subschemeMap_subschemeι,
          Category.assoc] }

/-- The projection of `Stacks.Thickenings.imageSubschemeCone` to a stage, followed by the
inclusion of the scheme-theoretic image, is the closed immersion followed by the projection. -/
theorem imageSubschemeCone_fac {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u}) (c : Cone D)
    {Z : Scheme.{u}} (i : Z ⟶ c.pt) [IsClosedImmersion i] (j : J) :
    (imageSubschemeCone D c i).π.app j ≫ (i.ker.map (c.π.app j)).subschemeι = i ≫ c.π.app j :=
  IsClosedImmersion.lift_fac (i.ker.map (c.π.app j)).subschemeι (i ≫ c.π.app j) _

/-- **A closed subscheme of the limit is the limit of its scheme-theoretic images in the
stages.** This is the step of the proof of [Stacks Project, Tag 09MW] which writes the closed
subscheme of a thickening as a limit over the approximating system of the ambient scheme.

A competing cone maps to the limit, and its ideal sheaf there is contained in the ideal sheaf of
the closed subscheme: that containment is `AlgebraicGeometry.le_iSup_comap_map_of_isLimit`, which
says the ideal sheaf of the closed subscheme is the supremum of the inverse images of its images
in the stages, together with the fact that each projection of the competing cone factors through
the corresponding scheme-theoretic image. -/
noncomputable def imageSubschemeConeIsLimit
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    {Z : Scheme.{u}} (i : Z ⟶ c.pt) [IsClosedImmersion i] :
    IsLimit (imageSubschemeCone D c i) := by
  have hci : IsClosedImmersion i := inferInstance
  let a := imageSubschemeInclusion D c i.ker
  let f (s : Cone (imageSubschemeDiagram D c i.ker)) := hc.lift ((Cone.postcompose a).obj s)
  have hf (s : Cone (imageSubschemeDiagram D c i.ker)) : i.ker ≤ (f s).ker := by
    refine le_trans (AlgebraicGeometry.le_iSup_comap_map_of_isLimit D c hc i.ker) ?_
    refine iSup_le fun j => ?_
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_ker (f s) (c.π.app j),
      show f s ≫ c.π.app j = s.π.app j ≫ (i.ker.map (c.π.app j)).subschemeι from hc.fac _ j]
    exact (Scheme.IdealSheafData.ker_subschemeι (i.ker.map (c.π.app j))).ge.trans
      (Scheme.Hom.le_ker_comp (s.π.app j) (i.ker.map (c.π.app j)).subschemeι)
  refine { lift := fun s => @IsClosedImmersion.lift _ _ _ i (f s) hci (hf s)
           fac := ?_, uniq := ?_ }
  · intro s j
    apply (cancel_mono (i.ker.map (c.π.app j)).subschemeι).1
    rw [Category.assoc, imageSubschemeCone_fac, ← Category.assoc,
      IsClosedImmersion.lift_fac]
    exact hc.fac _ j
  · intro s m hm
    have key : m ≫ i = @IsClosedImmersion.lift _ _ _ i (f s) hci (hf s) ≫ i := by
      rw [IsClosedImmersion.lift_fac]
      refine hc.hom_ext fun j => ?_
      rw [Category.assoc, ← imageSubschemeCone_fac, ← Category.assoc, hm]
      exact (hc.fac ((Cone.postcompose a).obj s) j).symm
    exact (cancel_mono i).1 key

/-! ### The ascent along a thickening of the limit of a Noetherian system -/

/-- **Quasi-affineness ascends along a thickening of the limit of a directed system of Noetherian
schemes with affine transition morphisms.**

This is the limit argument of [Stacks Project, Tag 09MW] at `L = 𝒪`. The closed subscheme is the
limit of its scheme-theoretic images in the stages
(`Stacks.Thickenings.imageSubschemeConeIsLimit`), so one of those images is quasi-affine by
[Stacks Project, Tag 01Z5]; the image of the limit lies in the support of its ideal sheaf, which
is constructible in a Noetherian stage, so by [Stacks Project, Tag 05F4] a later stage maps into
it, and the fibre product of that stage with the image is a thickening of it which is quasi-affine
over the image. The stage is Noetherian, so
`Stacks.Thickenings.isQuasiAffine_of_isThickening_of_isLocallyNoetherian` applies to that
thickening, and the limit is affine over the stage. -/
theorem isQuasiAffine_of_isThickening_of_descentSituation
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (d : AlgebraicGeometry.DescentSituation.{u, u} J)
    (hN : ∀ j : Jᵒᵖ, IsNoetherian (d.system.obj j))
    {Z : Scheme.{u}} (i : Z ⟶ d.limitCone.pt) (hi : IsThickening i)
    [Scheme.IsQuasiAffine Z] : Scheme.IsQuasiAffine d.limitCone.pt := by
  classical
  have : IsClosedImmersion i := hi.1
  have : Surjective i := ⟨hi.2⟩
  have : Nonempty J := ⟨d.base⟩
  have : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), IsAffineHom (d.system.map f) := d.transition_affine
  have : ∀ j : Jᵒᵖ, CompactSpace (d.system.obj j) := fun j => d.quasiCompact j.unop
  have : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (d.system.obj j) := fun j => d.quasiSeparated j.unop
  let E := imageSubschemeDiagram d.system d.limitCone i.ker
  let a := imageSubschemeInclusion d.system d.limitCone i.ker
  let c := imageSubschemeCone d.system d.limitCone i
  have hacl : ∀ j : Jᵒᵖ, IsClosedImmersion (a.app j) := fun j ↦
    inferInstanceAs (IsClosedImmersion (i.ker.map (d.limitCone.π.app j)).subschemeι)
  have (j : Jᵒᵖ) : IsNoetherian (E.obj j) := by
    have : IsLocallyNoetherian (E.obj j) := LocallyOfFiniteType.isLocallyNoetherian (a.app j)
    have : CompactSpace (E.obj j) := QuasiCompact.compactSpace_of_compactSpace (a.app j)
    exact {}
  have : ∀ {j k : Jᵒᵖ} (g : j ⟶ k), IsAffineHom (E.map g) := by
    intro j k g
    have : IsAffineHom (E.map g ≫ a.app k) := by
      rw [a.naturality g]
      infer_instance
    exact IsAffineHom.of_comp _ (a.app k)
  have : Scheme.IsQuasiAffine c.pt := ‹Scheme.IsQuasiAffine Z›
  obtain ⟨j, hj⟩ := Scheme.exists_isQuasiAffine_of_isLimit E c
    (imageSubschemeConeIsLimit d.system d.limitCone d.isLimit i)
  let dj : AlgebraicGeometry.DescentSituation.{u, u} J := { d with base := j.unop }
  let S : Set (d.system.obj (op j.unop)) :=
    (i.ker.map (d.limitCone.π.app (op j.unop))).support
  have hS : Topology.IsLocallyConstructible S := by
    refine Topology.IsConstructible.isLocallyConstructible (Topology.IsConstructible.of_compl ?_)
    exact (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible
      (i.ker.map (d.limitCone.π.app (op j.unop))).support.isClosed.isOpen_compl
  have hlim : Set.range (dj.limitCone.π.app (op dj.base)).base ⊆ S := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (show Function.Surjective i from Surjective.surj (f := i)) x
    have h := Scheme.Hom.range_subset_ker_support (i ≫ d.limitCone.π.app (op j.unop))
    exact (show Set.range (i ≫ d.limitCone.π.app (op j.unop)) ⊆ S by
      simpa [S, Scheme.Hom.ker_comp] using h) ⟨z, rfl⟩
  obtain ⟨l, hl, hlS⟩ :=
    (AlgebraicGeometry.eventually_range_transition_subset_of_isLocallyConstructible dj S hS
      hlim).exists
  let g := d.system.map (homOfLE hl).op
  have : IsAffineHom g := d.transition_affine _
  have : Surjective (pullback.fst g (a.app (op j.unop))) := by
    refine ⟨fun x ↦ ?_⟩
    change x ∈ Set.range (pullback.fst g (a.app (op j.unop))).base
    rw [Scheme.Pullback.range_fst]
    change g x ∈ Set.range (i.ker.map (d.limitCone.π.app (op j.unop))).subschemeι.base
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hlS ⟨x, rfl⟩
  have : Scheme.IsQuasiAffine (E.obj (op j.unop)) := hj
  have : IsAffineHom (pullback.snd g (a.app (op j.unop))) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g (a.app (op j.unop))) inferInstance
  have : Scheme.IsQuasiAffine (pullback g (a.app (op j.unop))) :=
    Scheme.IsQuasiAffine.of_isAffineHom (pullback.snd g (a.app (op j.unop)))
  have : Scheme.IsQuasiAffine (d.system.obj (op l)) :=
    isQuasiAffine_of_isThickening_of_isLocallyNoetherian
      (show IsThickening (pullback.fst g (a.app (op j.unop))) from
        ⟨inferInstance, Surjective.surj⟩)
  have : IsAffineHom (d.limitCone.π.app (op l)) :=
    AlgebraicGeometry.isAffineHom_π_app d.system d.limitCone d.isLimit (op l)
  exact Scheme.IsQuasiAffine.of_isAffineHom (d.limitCone.π.app (op l))

/-! ### The ascent along an arbitrary thickening -/

/-- **Quasi-affineness ascends along an arbitrary thickening.** For a closed immersion
`k : Y ⟶ Y'` surjective on points with `Y` quasi-affine, `Y'` is quasi-affine. No Noetherian
hypothesis, and no hypothesis on the kernel ideal sheaf.

`Y'` is quasi-compact and quasi-separated, being homeomorphic to `Y`; absolute Noetherian
approximation ([Stacks Project, Tag 01ZA]) presents it as the limit of a directed system of
schemes of finite type over the integers with affine transition morphisms, every one of which is
Noetherian, and `Stacks.Thickenings.isQuasiAffine_of_isThickening_of_descentSituation` applies to
that presentation. -/
theorem isQuasiAffine_of_isThickening {Y Y' : Scheme.{u}} {k : Y ⟶ Y'} (hk : IsThickening k)
    [Scheme.IsQuasiAffine Y] : Scheme.IsQuasiAffine Y' := by
  classical
  have : IsClosedImmersion k := hk.1
  have : CompactSpace Y' := hk.homeomorph.compactSpace
  have : QuasiSeparatedSpace Y' := (quasiSeparatedSpace_congr hk.homeomorph).mp inferInstance
  obtain ⟨I, hpre, hne, hdir, F, cc, hAff, hFT, hQC, ⟨hcc⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType Y'
  let e : Iᵒᵖ ≌ Iᵒᵈ := (orderDualEquivalence I).symm
  have (j : Iᵒᵖ) : IsNoetherian (F.obj (e.functor.obj j)) :=
    have := hFT (e.functor.obj j)
    have := hQC (e.functor.obj j)
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from _
  let d : AlgebraicGeometry.DescentSituation.{u, u} I :=
    { system := e.functor ⋙ F
      transition_affine := fun f => hAff (e.functor.map f)
      quasiCompact := fun j => inferInstanceAs (CompactSpace (F.obj (e.functor.obj (op j))))
      quasiSeparated := fun j =>
        inferInstanceAs (QuasiSeparatedSpace (F.obj (e.functor.obj (op j))))
      limitCone := Cone.whisker e.functor (Cone.mk Y' cc)
      isLimit := hcc.whiskerEquivalence e
      base := Classical.arbitrary I }
  exact isQuasiAffine_of_isThickening_of_descentSituation d
    (fun j => inferInstanceAs (IsNoetherian (F.obj (e.functor.obj j)))) k hk

/-- **The ascent of quasi-affineness along a thickening, discharged.** This is
`Stacks.Thickenings.QuasiAffineAscendsAlongThickening`, the statement part (9) of
[Stacks Project, Tag 09ZV] was reduced to, proved by
`Stacks.Thickenings.isQuasiAffine_of_isThickening`. -/
theorem quasiAffineAscendsAlongThickening : QuasiAffineAscendsAlongThickening.{u} :=
  fun _ _ _ hk _ => isQuasiAffine_of_isThickening hk

/-- **[Stacks Project, Tag 0B7L].** For a closed immersion inducing a homeomorphism of underlying
spaces — equivalently, a surjective closed immersion — the ambient scheme is quasi-affine if and
only if the closed subscheme is. No Noetherian hypothesis.

*Ambient `⟹` closed subscheme* is the elementary implication, a closed immersion being affine
(`Stacks.Thickenings.isQuasiAffine_of_isQuasiAffine_ambient`); *closed subscheme `⟹` ambient* is
`Stacks.Thickenings.isQuasiAffine_of_isThickening`. This supersedes the Noetherian
`Stacks.Thickenings.isQuasiAffine_iff_of_isNoetherian`, which is
[Stacks Project, Tag 0B7K]. -/
@[stacks 0B7L]
theorem isQuasiAffine_iff_of_isThickening {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}
    (hk : IsThickening k) : Scheme.IsQuasiAffine Y' ↔ Scheme.IsQuasiAffine Y :=
  ⟨fun hY' => isQuasiAffine_of_isQuasiAffine_ambient hk hY',
    fun _ => isQuasiAffine_of_isThickening hk⟩

/-! ### Part (9) of [Stacks Project, Tag 09ZV] -/

/-- **Part (9) of [Stacks Project, Tag 09ZV].** For a morphism of thickenings — a commutative
square whose horizontal arrows are thickenings — the morphism of closed subschemes is
quasi-affine if and only if the morphism of ambient schemes is. No hypothesis on the schemes.

The `mpr` half is `Stacks.Thickenings.isQuasiAffineHom_left_of_right`, which needs nothing; the
`mp` half is `Stacks.Thickenings.isQuasiAffineHom_right_of_left` fed the absolute statement
`Stacks.Thickenings.quasiAffineAscendsAlongThickening`. -/
@[stacks 09ZV "quasi_affine"]
theorem isQuasiAffineHom_left_iff_right {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j) (φ : Arrow.mk i ⟶ Arrow.mk j) :
    IsQuasiAffineHom φ.left ↔ IsQuasiAffineHom φ.right :=
  isQuasiAffineHom_left_iff_right_of_ascends quasiAffineAscendsAlongThickening hi hj φ

end Stacks.Thickenings

end
