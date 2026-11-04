module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitConverse

/-!
# The colimit of Stacks 0AIU in fppf sheaves

Let `𝔛` be a formal scheme in the sense of McQuillan. Stacks 0AIU and 0AIV ask that the functor of
points `h_𝔛` be a colimit, *in the category of fppf sheaves*, of a directed system of schemes `X_λ`
along thickenings: the comparison map `colim h_{X_λ} → h_𝔛` from the presheaf colimit becomes an
isomorphism after fppf sheafification, that is, it is fppf locally injective and fppf locally
surjective. `AlgebraicGeometry.McQuillanFormalScheme.IsColimitOfThickenings` asks the same for the
Zariski topology. This file shows the two conditions agree.

A Zariski covering is an fppf covering, so the Zariski condition implies the fppf one. Conversely,
suppose the comparison map is fppf locally bijective.

* Each stage `h_{X_λ} → h_𝔛` is injective: two morphisms `T → X_λ` with the same image in `h_𝔛`
  agree fppf locally in the filtered colimit, hence after a transition `X_λ → X_μ`, which is a
  thickening and so a monomorphism; `h_{X_λ}` being an fppf sheaf, they agree. Therefore the
  comparison map is injective, and in particular Zariski locally injective.
* Over a quasi-compact scheme `T`, every point `s` of `h_𝔛(T)` comes from a single stage: an fppf
  covering of `T` on whose members `s` lifts to stages consists of flat morphisms locally of finite
  presentation, which are open, so finitely many of them cover `T`; their lifts all land in one
  stage `X_μ`, and agree on overlaps because the stage `h_{X_μ} → h_𝔛` is injective; they glue
  since `h_{X_μ}` is an fppf sheaf, and the glued morphism maps to `s` because `h_𝔛` is fpqc
  separated. Covering an arbitrary scheme by affine opens, the comparison map is Zariski locally
  surjective.

## Main definitions

* `AlgebraicGeometry.McQuillanFormalScheme.IsFppfColimitOfThickenings`: `h_𝔛` is a colimit of
  schemes along thickenings in fppf sheaves.

## Main results

* `AlgebraicGeometry.McQuillanFormalScheme.injective_coconeMap_app_of_isLocallyInjective`: for a
  subcanonical topology for which the comparison map is locally injective, the stages are
  injective.
* `AlgebraicGeometry.McQuillanFormalScheme.exists_coconeMap_app_eq_of_compactSpace`: if the
  comparison map is fppf locally surjective and the stages are injective, a point over a
  quasi-compact scheme comes from a single stage.
* `AlgebraicGeometry.McQuillanFormalScheme.isFppfColimitOfThickenings_iff`: the fppf and the
  Zariski colimit conditions agree.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Every Zariski covering sieve is an fppf covering sieve. -/
theorem Scheme.zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

/-- **The functor of points of a McQuillan formal scheme is a colimit of schemes along thickenings
in fppf sheaves, as in Stacks 0AIU**: there are a nonempty directed preorder `Λ`, a system
`λ ↦ X_λ` of schemes whose transition morphisms are thickenings, and morphisms `h_{X_λ} → h_𝔛`
compatible with the transitions, such that the comparison map `colim h_{X_λ} → h_𝔛` from the
presheaf colimit is fppf locally injective and fppf locally surjective. A morphism of presheaves
induces an isomorphism of fppf sheafifications exactly when it is fppf locally bijective, so this
says that `h_𝔛` is the colimit of the `h_{X_λ}` in fppf sheaves. -/
def McQuillanFormalScheme.IsFppfColimitOfThickenings (𝔛 : McQuillanFormalScheme.{u}) : Prop :=
  ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
    (D : Λ ⥤ Scheme.{u}) (_ : ∀ ⦃i j : Λ⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening (D.map g))
    (ι : D ⋙ yoneda ⟶ (Functor.const Λ).obj (mcQuillanFormalSchemePoints 𝔛)),
    Presheaf.IsLocallyInjective Scheme.fppfTopology
        (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)) ∧
      Presheaf.IsLocallySurjective Scheme.fppfTopology
        (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι))

namespace McQuillanFormalScheme

open LocallyTopologicallyRingedSpace.IdealSheaf

/-- Every element of the presheaf colimit over `T` comes from some stage. -/
private theorem exists_colimit_ι_app_eq {J : Type u} [SmallCategory J] {F : J ⥤ Scheme.{u}}
    (T : Scheme.{u}) (x : (colimit (F ⋙ yoneda)).obj (op T)) :
    ∃ (l : J) (a : T ⟶ F.obj l), (colimit.ι (F ⋙ yoneda) l).app (op T) a = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ (Type u)).obj (op T)) (colimit.isColimit (F ⋙ yoneda))) x

variable {𝔛 : McQuillanFormalScheme.{u}} {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
  [Nonempty Λ] {D : Λ ⥤ Scheme.{u}}
  (ι : D ⋙ yoneda ⟶ (Functor.const Λ).obj (mcQuillanFormalSchemePoints 𝔛))
  (hD : ∀ ⦃i j : Λ⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening (D.map g))

include hD in
/-- **The stages of the colimit are injective** for any subcanonical topology `J` for which the
comparison map is locally injective: two morphisms `T → X_λ` with the same image in `h_𝔛` agree
`J`-locally in the filtered colimit, hence after some transition `X_λ → X_μ`, which is a thickening
and hence a monomorphism, and `h_{X_λ}` is a `J`-sheaf. -/
theorem injective_coconeMap_app_of_isLocallyInjective (J : GrothendieckTopology Scheme.{u})
    [J.Subcanonical]
    (hinj : Presheaf.IsLocallyInjective J (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι))) (l : Λ)
    (T : Scheme.{u}) : Function.Injective ((ι.app l).app (op T)) := by
  intro a b hab
  have hS := Presheaf.equalizerSieve_mem J
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι))
    ((colimit.ι (D ⋙ yoneda) l).app (op T) a) ((colimit.ι (D ⋙ yoneda) l).app (op T) b)
    ((colimitDesc_app_ι ι l a).trans (hab.trans (colimitDesc_app_ι ι l b).symm))
  have hsh : Presieve.IsSheaf J (yoneda.obj (D.obj l)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  refine (hsh _ hS).isSeparatedFor.ext fun U f hf => ?_
  have hf' : (colimit.ι (D ⋙ yoneda) l).app (op U) (f ≫ a) =
      (colimit.ι (D ⋙ yoneda) l).app (op U) (f ≫ b) :=
    (NatTrans.naturality_apply (colimit.ι (D ⋙ yoneda) l) f.op a).trans
      (hf.trans (NatTrans.naturality_apply (colimit.ι (D ⋙ yoneda) l) f.op b).symm)
  obtain ⟨m, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ (Type u)).obj (op U))
      (colimit.isColimit (D ⋙ yoneda))) (f ≫ a) (f ≫ b)).mp hf'
  have := (hD g).1
  exact (cancel_mono (D.map g)).mp hg

omit [Nonempty Λ] in
/-- If the stages are injective, so is the comparison map from the colimit: two elements of the
colimit come from a common stage, the system being directed. -/
theorem injective_colimitDesc_app (hι : ∀ (l : Λ) (T : Scheme.{u}),
    Function.Injective ((ι.app l).app (op T))) (T : Scheme.{u}) :
    Function.Injective ((colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)).app (op T)) := by
  intro x y hxy
  obtain ⟨l, a, rfl⟩ := exists_colimit_ι_app_eq T x
  obtain ⟨m, b, rfl⟩ := exists_colimit_ι_app_eq T y
  rw [colimitDesc_app_ι, colimitDesc_app_ι] at hxy
  obtain ⟨n, hln, hmn⟩ := exists_ge_ge l m
  have hx := congrArg (fun η => η.app (op T) a) (colimit.w (D ⋙ yoneda) (homOfLE hln))
  have hy := congrArg (fun η => η.app (op T) b) (colimit.w (D ⋙ yoneda) (homOfLE hmn))
  refine hx.symm.trans (Eq.trans ?_ hy)
  refine congrArg ((colimit.ι (D ⋙ yoneda) n).app (op T))
    (show a ≫ D.map (homOfLE hln) = b ≫ D.map (homOfLE hmn) from hι n T ?_)
  exact (coconeMap_app_comp_map ι _ a).trans (hxy.trans (coconeMap_app_comp_map ι _ b).symm)

omit [IsDirected Λ (· ≤ ·)] [Nonempty Λ] in
/-- If the comparison map is fppf locally surjective, every point of `𝔛` lifts to some stage along
the members of an fppf covering. -/
theorem exists_fppfCover_coconeMap_app_eq
    (hsurj : Presheaf.IsLocallySurjective Scheme.fppfTopology
      (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)))
    {T : Scheme.{u}} (s : (mcQuillanFormalSchemePoints 𝔛).obj (op T)) :
    ∃ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T)
      (m : 𝒰.I₀ → Λ) (a : ∀ j, 𝒰.X j ⟶ D.obj (m j)),
      ∀ j, (ι.app (m j)).app (op (𝒰.X j)) (a j) =
        (mcQuillanFormalSchemePoints 𝔛).map (𝒰.f j).op s := by
  have hS := Presheaf.imageSieve_mem Scheme.fppfTopology
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)) s
  have : MorphismProperty.IsStableUnderBaseChange
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.ContainsIdentities
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := ⟨fun _ => inferInstance⟩
  have : MorphismProperty.IsMultiplicative
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := {}
  have : MorphismProperty.IsMultiplicative
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.inf
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology
    (P := @Flat ⊓ @LocallyOfFinitePresentation) hS
  have hlift : ∀ j, ∃ (m : Λ) (a : 𝒰.X j ⟶ D.obj m), (ι.app m).app (op (𝒰.X j)) a =
      (mcQuillanFormalSchemePoints 𝔛).map (𝒰.f j).op s := by
    intro j
    obtain ⟨x, hx⟩ := h𝒰 _ _ (Presieve.ofArrows.mk j)
    obtain ⟨m, a, rfl⟩ := exists_colimit_ι_app_eq (𝒰.X j) x
    exact ⟨m, a, (colimitDesc_app_ι ι m a).symm.trans hx⟩
  choose m a ha using hlift
  exact ⟨𝒰, m, a, ha⟩

/-- **Over a quasi-compact scheme, every point of `𝔛` comes from a single stage**, if the
comparison map is fppf locally surjective and the stages are injective. The point lifts to stages
along the members of an fppf covering; these are open maps, so finitely many of them cover `T`, and
their lifts land in a common stage `X_μ`. The lifts agree on overlaps, the stage `h_{X_μ} → h_𝔛`
being injective, so they glue, `h_{X_μ}` being an fppf sheaf; the glued morphism maps to the point
since `h_𝔛` is fpqc separated. -/
theorem exists_coconeMap_app_eq_of_compactSpace
    (hsurj : Presheaf.IsLocallySurjective Scheme.fppfTopology
      (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)))
    (hι : ∀ (l : Λ) (T : Scheme.{u}), Function.Injective ((ι.app l).app (op T)))
    {T : Scheme.{u}} [CompactSpace T] (s : (mcQuillanFormalSchemePoints 𝔛).obj (op T)) :
    ∃ (μ : Λ) (c : T ⟶ D.obj μ), (ι.app μ).app (op T) c = s := by
  classical
  obtain ⟨𝒰, m, a, ha⟩ := exists_fppfCover_coconeMap_app_eq ι hsurj s
  have hopen : ∀ j, IsOpen (Set.range (𝒰.f j)) := fun j => by
    have := (𝒰.map_prop j).1
    have := (𝒰.map_prop j).2
    exact (𝒰.f j).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun j => Set.range (𝒰.f j)) hopen
    fun x _ => Set.mem_iUnion.2 (𝒰.exists_eq x)
  obtain ⟨μ, hμ⟩ := Finset.exists_le (t.image m)
  have hle : ∀ j : t, m j ≤ μ := fun j => hμ _ (Finset.mem_image_of_mem _ j.2)
  let b : ∀ j : t, 𝒰.X j ⟶ D.obj μ := fun j => a j ≫ D.map (homOfLE (hle j))
  have hb : ∀ j : t, (ι.app μ).app (op (𝒰.X j)) (b j) =
      (mcQuillanFormalSchemePoints 𝔛).map (𝒰.f j).op s := fun j =>
    (coconeMap_app_comp_map ι _ (a j)).trans (ha j)
  have hbc : ∀ (j : t) {Z : Scheme.{u}} (g : Z ⟶ 𝒰.X j), (ι.app μ).app (op Z) (g ≫ b j) =
      (mcQuillanFormalSchemePoints 𝔛).map (g ≫ 𝒰.f j).op s := fun j Z g =>
    (NatTrans.naturality_apply (ι.app μ) g.op (b j)).trans ((congrArg _ (hb j)).trans
      (Functor.map_comp_apply (mcQuillanFormalSchemePoints 𝔛) (𝒰.f j).op g.op s).symm)
  have hcov : Presieve.ofArrows (fun j : t => 𝒰.X j) (fun j => 𝒰.f j) ∈
      Scheme.fppfPrecoverage T := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => 𝒰.map_prop j⟩
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨j, hj⟩, hx⟩
  have hgen := Precoverage.generate_mem_toGrothendieck hcov
  have hshD : Presieve.IsSheaf Scheme.fppfTopology (yoneda.obj (D.obj μ)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hcompat : Presieve.Arrows.Compatible (yoneda.obj (D.obj μ)) (fun j : t => 𝒰.f j) b := by
    intro i j Z gi gj hij
    refine hι μ Z ?_
    change (ι.app μ).app (op Z) (gi ≫ b i) = (ι.app μ).app (op Z) (gj ≫ b j)
    rw [hbc i gi, hbc j gj, hij]
  obtain ⟨c, hc, -⟩ := (Presieve.isSheafFor_arrows_iff (P := yoneda.obj (D.obj μ))
    (π := fun j : t => 𝒰.f j)).mp (hshD.isSheafFor _ hgen) b hcompat
  refine ⟨μ, c, ?_⟩
  have hsep : Presieve.IsSeparatedFor (mcQuillanFormalSchemePoints 𝔛)
      (Presieve.ofArrows (fun j : t => 𝒰.X j) (fun j => 𝒰.f j)) :=
    Presieve.isSeparatedFor_iff_generate.mpr
      (Presieve.isSeparated_of_le _ Scheme.fppfTopology_le_fpqcTopology
        (isSeparated_fpqcTopology_mcQuillanFormalSchemePoints 𝔛) _ hgen)
  refine hsep.ext ?_
  rintro Y f ⟨j⟩
  exact (NatTrans.naturality_apply (ι.app μ) (𝒰.f j).op c).symm.trans
    ((congrArg ((ι.app μ).app (op (𝒰.X j))) (hc j)).trans (hb j))

/-- If the comparison map is fppf locally surjective and the stages are injective, the
comparison map is Zariski locally surjective: over each affine open of a scheme, a point comes
from a stage. -/
theorem isLocallySurjective_zariskiTopology_of_fppfTopology
    (hsurj : Presheaf.IsLocallySurjective Scheme.fppfTopology
      (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)))
    (hι : ∀ (l : Λ) (T : Scheme.{u}), Function.Injective ((ι.app l).app (op T))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)) := by
  refine ⟨fun {T} s => ?_⟩
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨T.affineCover, ?_⟩
  rintro _ _ ⟨j⟩
  obtain ⟨μ, c, hc⟩ := exists_coconeMap_app_eq_of_compactSpace ι hsurj hι
    ((mcQuillanFormalSchemePoints 𝔛).map (T.affineCover.f j).op s)
  exact ⟨(colimit.ι (D ⋙ yoneda) μ).app _ c, (colimitDesc_app_ι ι μ c).trans hc⟩

end McQuillanFormalScheme

/-- **The colimit of Stacks 0AIU may be taken in Zariski or in fppf sheaves.** The functor of
points of a McQuillan formal scheme is a colimit of schemes along thickenings in fppf sheaves if
and only if it is one in Zariski sheaves, for the same system. -/
theorem McQuillanFormalScheme.isFppfColimitOfThickenings_iff (𝔛 : McQuillanFormalScheme.{u}) :
    𝔛.IsFppfColimitOfThickenings ↔ 𝔛.IsColimitOfThickenings := by
  refine ⟨fun ⟨Λ, _, _, _, D, hD, ι, hinj, hsurj⟩ => ?_,
    fun ⟨Λ, _, _, _, D, hD, ι, hinj, hsurj⟩ => ?_⟩
  · have hι := injective_coconeMap_app_of_isLocallyInjective ι hD Scheme.fppfTopology hinj
    exact ⟨Λ, inferInstance, inferInstance, inferInstance, D, hD, ι,
      Presheaf.isLocallyInjective_of_injective _ _ fun ⟨T⟩ => injective_colimitDesc_app ι hι T,
      isLocallySurjective_zariskiTopology_of_fppfTopology ι hsurj hι⟩
  · exact ⟨Λ, inferInstance, inferInstance, inferInstance, D, hD, ι,
      ⟨fun x y h => Scheme.zariskiTopology_le_fppfTopology _ (hinj.equalizerSieve_mem x y h)⟩,
      Presheaf.isLocallySurjective_of_le Scheme.zariskiTopology_le_fppfTopology _ hsurj⟩

end AlgebraicGeometry

end
