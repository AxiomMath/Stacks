module

public import Mathlib.FieldTheory.Perfect
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Differentials
public import StacksFrontier.AlgebraicGeometry.Groupoids.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.LocallyFreeDifferentials
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.LocallyFreeDifferentialsPerfectField

/-!
# Smoothness of the source and target of a groupoid scheme on a field

Let `(U, R, s, t, c)` be a groupoid scheme over a scheme `S` whose scheme of objects `U` is the
spectrum of a field `k`, and whose source and target morphisms are locally of finite type. Then
`s` and `t` are smooth as soon as `k` has characteristic zero, and also as soon as `k` is perfect
and `R` is reduced.

Both statements come from the same computation: the sheaf of differentials `Ω_{R/U}` is free. The
morphism `s` is automatically flat, the local rings of `U` being fields, so the canonical
surjection of [Stacks Project, Tag 04R9] is an isomorphism `t^* 𝒞_{U/R} ≅ Ω_{R/U}`; the conormal
sheaf of the identity section is a quasi-coherent module on the spectrum of a field, hence free,
and the inverse image of a free module is free.

## Main results

* `Stacks.Groupoids.GroupoidScheme.exists_free_iso_relativeDifferentials_source_left`: **the
  sheaf of differentials of `R` over `U` is a free `𝒪_R`-module** when `U` is the spectrum of a
  field.
* `Stacks.Groupoids.GroupoidScheme.smooth_source_left_of_charZero` and
  `Stacks.Groupoids.GroupoidScheme.smooth_target_left_of_charZero`: **[Stacks Project, Tag
  04RA]**, smoothness of the source and of the target morphism in characteristic zero.
* `Stacks.Groupoids.GroupoidScheme.smooth_source_left_of_isReduced_of_perfectField` and
  `Stacks.Groupoids.GroupoidScheme.smooth_target_left_of_isReduced_of_perfectField`: **[Stacks
  Project, Tag 04RB]**, smoothness of the source and of the target morphism over a perfect field
  when the scheme of arrows is reduced.

## Implementation notes

That the scheme of objects is the spectrum of a field is expressed by an isomorphism
`G.objects.left ≅ Spec k`, as elsewhere for groupoid schemes on a field, and the hypotheses and
conclusions are imposed on the underlying morphisms of schemes rather than on their images in the
slice category over `S`.

Only the source morphism is assumed locally of finite type: the target morphism is the source
morphism precomposed with the inverse, which is an automorphism of the scheme of arrows, so the
two hypotheses are equivalent, and for the same reason smoothness of the target follows from
smoothness of the source.

The two smoothness criteria used, [Stacks Project, Tag 04QN] and [Stacks Project, Tag 04QP], are
stated for a morphism into `Spec k` itself, while the differentials that are computed are those
of `s : R ⟶ U`. The two are compared by the base change isomorphism of [Stacks Project, Tag 01V0]
applied to the square with top edge the identity of `R` and right edge the inverse of the given
isomorphism, which is cartesian because two of its edges are invertible.

## References

* [Stacks Project, Tag 04RA](https://stacks.math.columbia.edu/tag/04RA)
* [Stacks Project, Tag 04RB](https://stacks.math.columbia.edu/tag/04RB)
* [Stacks Project, Tag 04R9](https://stacks.math.columbia.edu/tag/04R9)
* [Stacks Project, Tag 04QN](https://stacks.math.columbia.edu/tag/04QN)
* [Stacks Project, Tag 04QP](https://stacks.math.columbia.edu/tag/04QP)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Modules on a scheme isomorphic to the spectrum of a field -/

/-- A quasi-coherent module on a scheme isomorphic to the spectrum of a field is free: its
inverse image on the spectrum of the field is quasi-coherent, hence free, and the module is the
inverse image of that along the isomorphism, while the inverse image of a free module is free. -/
private theorem exists_free_iso_of_isQuasicoherent_of_iso_spec_field {Y : Scheme.{u}}
    (k : Type u) [Field k] (e : Y ≅ Spec (.of k)) (N : Y.Modules) (hN : N.IsQuasicoherent) :
    ∃ I : Type u, Nonempty (N ≅ SheafOfModules.free (R := Y.ringCatSheaf) I) := by
  have := hN
  obtain ⟨I, ⟨h⟩⟩ := GroupSchemeDifferentials.exists_free_iso_of_isQuasicoherent_spec_field k
    ((Scheme.Modules.pullback e.inv).obj N)
  exact ⟨I, ⟨((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr (show 𝟙 Y = e.hom ≫ e.inv by simp)).app N ≪≫
    ((Scheme.Modules.pullbackComp e.hom e.inv).app N).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso h ≪≫ Scheme.Modules.pullbackFreeIso e.hom I⟩⟩

/-- A module isomorphic to a free module is locally free: its restriction to any open is the
inverse image of a free module, hence free. -/
private theorem isLocallyFree_of_free_iso {X : Scheme.{u}} (F : X.Modules) {I : Type u}
    (h : F ≅ SheafOfModules.free (R := X.ringCatSheaf) I) :
    SheafOfModules.IsLocallyFree.{u, u, u} F :=
  (Stacks.Modules.isLocallyFree_iff_localGenerators F).mp fun _ =>
    ⟨⊤, trivial, I, ⟨(Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app F ≪≫
      (Scheme.Modules.pullback (⊤ : X.Opens).ι).mapIso h ≪≫
      Scheme.Modules.pullbackFreeIso (⊤ : X.Opens).ι I⟩⟩

/-- A morphism into a scheme isomorphic to the spectrum of a field is flat: the local rings of
the spectrum of a field are fields, and a module over a field is flat. -/
@[ega "IV 11.9.9" "Parenthetical clause"]
private theorem flat_of_iso_spec_field {X Y : Scheme.{u}} {k : Type u} [Field k]
    (e : Y ≅ Spec (.of k)) (f : X ⟶ Y) : Flat f := by
  have : Flat (f ≫ e.hom) := flat_of_isField_stalk _ fun _ => isField_stalk_Spec_field k _
  have h : Flat ((f ≫ e.hom) ≫ e.inv) := inferInstance
  simpa using h

/-- Changing the base of the relative differentials along an isomorphism of the base does not
change them: the square with top edge the identity, left edge `a ≫ b`, right edge `a` and bottom
edge the inverse of `b` is cartesian, so the base change map of [Stacks Project, Tag 01V0] for it
is an isomorphism. -/
private noncomputable def relativeDifferentialsIsoCompIsIso {X Y Z : Scheme.{u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) [IsIso b] :
    Scheme.Hom.relativeDifferentials a ≅ Scheme.Hom.relativeDifferentials (a ≫ b) :=
  let hsq : IsPullback (𝟙 X) (a ≫ b) a (inv b) := IsPullback.of_horiz_isIso ⟨by simp⟩
  let : IsIso (Scheme.Hom.relativeDifferentialsMap (𝟙 X) a (a ≫ b) (inv b) hsq.w) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback (𝟙 X) (a ≫ b) a (inv b) hsq
  ((Scheme.Modules.pullbackId X).app (Scheme.Hom.relativeDifferentials a)).symm ≪≫
    asIso (Scheme.Hom.relativeDifferentialsMap (𝟙 X) a (a ≫ b) (inv b) hsq.w)

/-- A morphism is smooth if its composite with an isomorphism is smooth. -/
private theorem smooth_of_smooth_comp_iso {X Y Z : Scheme.{u}} {f : X ⟶ Y} (g : Y ⟶ Z) [IsIso g]
    (h : Smooth (f ≫ g)) : Smooth f := by
  have : Smooth ((f ≫ g) ≫ inv g) := inferInstance
  simpa using this

end AlgebraicGeometry

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]

/-! ### Freeness of the sheaf of differentials -/

/-- **The sheaf of differentials of the scheme of arrows of a groupoid scheme on a field is
free.** For a groupoid scheme whose scheme of objects `U` is the spectrum of a field, `Ω_{R/U}`
is a free `𝒪_R`-module, the differentials being taken relative to the source morphism.

The source morphism is flat, the local rings of `U` being fields, so the canonical surjection of
[Stacks Project, Tag 04R9] is an isomorphism `t^* 𝒞_{U/R} ≅ Ω_{R/U}`. The conormal sheaf of the
identity section is quasi-coherent, hence free on the spectrum of a field, and the inverse image
of a free module is free. -/
theorem exists_free_iso_relativeDifferentials_source_left
    (e : G.objects.left ≅ Spec (.of k)) :
    ∃ I : Type u, Nonempty (Scheme.Hom.relativeDifferentials G.source.left ≅
      SheafOfModules.free (R := G.arrows.left.ringCatSheaf) I) := by
  have : Flat G.source.left := flat_of_iso_spec_field e G.source.left
  obtain ⟨I, ⟨hc⟩⟩ := exists_free_iso_of_isQuasicoherent_of_iso_spec_field k e
    (Stacks.Conormal.conormalSheaf G.identity.left)
    (Stacks.Conormal.conormalSheaf_isQuasicoherent G.identity.left)
  have hiso := G.isIso_conormalToDifferentials
  refine ⟨I, ⟨(@asIso _ _ _ _ G.conormalToDifferentials hiso).symm ≪≫ ?_⟩⟩
  exact (Scheme.Modules.pullback G.target.left).mapIso hc ≪≫
    Scheme.Modules.pullbackFreeIso G.target.left I

/-- The sheaf of differentials of the scheme of arrows relative to the spectrum of the field
itself is locally free, read off the freeness of `Ω_{R/U}` through the base change isomorphism of
[Stacks Project, Tag 01V0] along the given isomorphism `U ≅ Spec k`. -/
private theorem isLocallyFree_relativeDifferentials_source_left_comp
    (e : G.objects.left ≅ Spec (.of k)) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (Scheme.Hom.relativeDifferentials (G.source.left ≫ e.hom)) := by
  obtain ⟨I, ⟨hfree⟩⟩ := G.exists_free_iso_relativeDifferentials_source_left e
  exact isLocallyFree_of_free_iso _
    ((relativeDifferentialsIsoCompIsIso G.source.left e.hom).symm ≪≫ hfree)

/-- Smoothness of the target morphism follows from smoothness of the source morphism: the target
morphism is the source morphism precomposed with the inverse, which is an automorphism of the
scheme of arrows. -/
private theorem smooth_target_left_of_smooth_source_left (h : Smooth G.source.left) :
    Smooth G.target.left := by
  have := h
  have := groupoidInverse_left_isIso G
  have hcomp : G.inverse.left ≫ G.source.left = G.target.left := by
    rw [← Over.comp_left, G.source_inverse]
  rw [← hcomp]
  infer_instance

/-! ### Smoothness in characteristic zero -/

/-- **[Stacks Project, Tag 04RA]: the source morphism of a groupoid scheme on a field of
characteristic zero is smooth.** If the scheme of objects of a groupoid scheme is the spectrum of
a field of characteristic zero and the source morphism is locally of finite type, then the source
morphism is smooth.

The sheaf of differentials `Ω_{R/U}` is free by
`Stacks.Groupoids.GroupoidScheme.exists_free_iso_relativeDifferentials_source_left`, and a
scheme locally of finite type over a field of characteristic zero whose differentials are locally
free is smooth by [Stacks Project, Tag 04QN]. -/
@[stacks 04RA "the source morphism", sga "3 VIB 1.6" "special case", sga "3 XVII 5.5" "partial"]
theorem smooth_source_left_of_charZero [CharZero k] (e : G.objects.left ≅ Spec (.of k))
    [LocallyOfFiniteType G.source.left] : Smooth G.source.left := by
  exact smooth_of_smooth_comp_iso e.hom
    (smooth_of_isLocallyFree_relativeDifferentials_of_charZero _
      (G.isLocallyFree_relativeDifferentials_source_left_comp e))

/-- **[Stacks Project, Tag 04RA]: the target morphism of a groupoid scheme on a field of
characteristic zero is smooth.** This is the previous statement transported along the inverse,
which is an automorphism of the scheme of arrows carrying the source morphism to the target
morphism. -/
@[stacks 04RA "the target morphism", sga "3 XVII 5.5" "partial"]
theorem smooth_target_left_of_charZero [CharZero k] (e : G.objects.left ≅ Spec (.of k))
    [LocallyOfFiniteType G.source.left] : Smooth G.target.left :=
  G.smooth_target_left_of_smooth_source_left (G.smooth_source_left_of_charZero e)

/-! ### Smoothness over a perfect field -/

/-- **[Stacks Project, Tag 04RB]: the source morphism of a groupoid scheme with reduced scheme of
arrows on a perfect field is smooth.** If the scheme of objects of a groupoid scheme is the
spectrum of a perfect field, the source morphism is locally of finite type and the scheme of
arrows is reduced, then the source morphism is smooth.

The sheaf of differentials `Ω_{R/U}` is free by
`Stacks.Groupoids.GroupoidScheme.exists_free_iso_relativeDifferentials_source_left`, and a
reduced scheme locally of finite type over a perfect field whose differentials are locally free
is smooth by [Stacks Project, Tag 04QP]. -/
@[stacks 04RB "the source morphism"]
theorem smooth_source_left_of_isReduced_of_perfectField [PerfectField k]
    (e : G.objects.left ≅ Spec (.of k)) [IsReduced G.arrows.left]
    [LocallyOfFiniteType G.source.left] : Smooth G.source.left := by
  exact smooth_of_smooth_comp_iso e.hom
    (smooth_of_isLocallyFree_relativeDifferentials_of_perfectField _
      (G.isLocallyFree_relativeDifferentials_source_left_comp e))

/-- **[Stacks Project, Tag 04RB]: the target morphism of a groupoid scheme with reduced scheme of
arrows on a perfect field is smooth.** This is the previous statement transported along the
inverse, which is an automorphism of the scheme of arrows carrying the source morphism to the
target morphism. -/
@[stacks 04RB "the target morphism"]
theorem smooth_target_left_of_isReduced_of_perfectField [PerfectField k]
    (e : G.objects.left ≅ Spec (.of k)) [IsReduced G.arrows.left]
    [LocallyOfFiniteType G.source.left] : Smooth G.target.left :=
  G.smooth_target_left_of_smooth_source_left
    (G.smooth_source_left_of_isReduced_of_perfectField e)

end Stacks.Groupoids.GroupoidScheme

end
