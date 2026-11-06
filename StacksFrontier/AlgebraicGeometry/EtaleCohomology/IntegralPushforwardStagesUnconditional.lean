module
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkIntegral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardStages
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardStages

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSitesUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.LimitPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional

/-!
# Restriction stalk maps and empty sections, for sheaves in a general universe

For sheaves of sets valued in `Type (max (u + 1) v)` on the small étale sites of a big étale
site: the map from the stalk of the restriction of a sheaf along an étale morphism to the stalk
of the sheaf, the existence of a section over an object with empty underlying scheme, and the
nonemptiness of the stalk of a direct image along an integral morphism at a geometric point with
no lift.

## Main definitions

* `AlgebraicGeometry.smallEtaleRestrictionStalkMapUniv` — the map from the stalk of a restriction
  to the stalk of the sheaf.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionStalkMap_germ_univ` — that map on germs.
* `AlgebraicGeometry.nonempty_sections_of_isEmpty_univ` — sections over an empty object.
* `AlgebraicGeometry.nonempty_etaleStalk_pushforward_of_isEmpty_lifts_univ` — nonemptiness of
  the stalk of an integral direct image at a geometric point with no lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section Restriction

variable {T' T : B.Scheme} (k : T' ⟶ T) [Etale (B.inclusion.map k)]

/-- The canonical map from the stalk at `x` of the restriction of a sheaf along an étale
morphism `k` to the stalk of the sheaf at `z = x ∘ k`, sending a germ to the germ of the same
section. -/
def smallEtaleRestrictionStalkMapUniv {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ B.inclusion.obj T') (z : Spec (.of K) ⟶ B.inclusion.obj T)
    (hz : x ≫ B.inclusion.map k = z)
    (H : Sheaf (SmallEtale.topology B T.1 T.property) (Type (max (u + 1) v))) :
    etaleStalk B T'.1 T'.property ⟨K, x⟩ ((smallEtaleRestrictionAlong B k _).obj H).obj ⟶
      etaleStalk B T.1 T.property ⟨K, z⟩ H.obj :=
  colimit.pre ((CategoryOfElements.π (geometricPointFiber B T.1 T.property ⟨K, z⟩)).op ⋙ H.obj)
    (smallEtaleRestrictionNeighborhoods B k x z hz).op

/-- **The restriction stalk map on germs.** The germ at a neighbourhood `A` of `x` of a section
of the restriction is the germ, at `A` regarded as a neighbourhood of `z`, of the same section. -/
theorem smallEtaleRestrictionStalkMap_germ_univ {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ B.inclusion.obj T') (z : Spec (.of K) ⟶ B.inclusion.obj T)
    (hz : x ≫ B.inclusion.map k = z)
    (H : Sheaf (SmallEtale.topology B T.1 T.property) (Type (max (u + 1) v)))
    (A : (geometricPointFiber B T'.1 T'.property ⟨K, x⟩).Elements)
    (s : H.obj.obj (op ((smallEtalePostcompose B T.1 T.property
      (SmallEtale.ofEtaleHom B k)).obj A.1))) :
    smallEtaleRestrictionStalkMapUniv B k x z hz H
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B T'.1 T'.property ⟨K, x⟩)).op ⋙
          ((smallEtaleRestrictionAlong B k _).obj H).obj) (op A) s) =
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B T.1 T.property ⟨K, z⟩)).op ⋙ H.obj)
        (op ((smallEtaleRestrictionNeighborhoods B k x z hz).obj A)) s :=
  ConcreteCategory.congr_hom (colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B T.1
    T.property ⟨K, z⟩)).op ⋙ H.obj) (smallEtaleRestrictionNeighborhoods B k x z hz).op (op A)) s

end Restriction

section Empty

/-- **A sheaf of sets has a section over an empty object.** The empty family is an étale
covering of an étale scheme with empty underlying scheme, and the empty family of sections is
compatible, so it has an amalgamation. -/
theorem nonempty_sections_of_isEmpty_univ (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (max (u + 1) v)))
    (U : SmallEtale B S hS) (hU : IsEmpty ((SmallEtale.toScheme B S hS).obj U)) :
    Nonempty (F.obj.obj (op U)) := by
  let E : PreZeroHypercover.{u + 1} U :=
    { I₀ := PEmpty.{u + 2}, X := fun i => PEmpty.elim i, f := fun i => PEmpty.elim i }
  have hE : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U) :=
    (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) _).2
      ⟨fun p => (hU.false p).elim, fun i => PEmpty.elim i⟩
  let t (i : E.I₀) : PUnit.{max (u + 1) v + 1} ⟶ F.obj.obj (op (E.X i)) := PEmpty.elim i
  obtain ⟨s, -, -⟩ := F.property.existsUnique_amalgamation_ofArrows E.f
    (_root_.AlgebraicGeometry.smallEtale_generate_covering B S hS U E hE) t
    (fun {_} i => PEmpty.elim i)
  exact ⟨s PUnit.unit⟩

/-- **The stalk of an integral direct image at a geometric point with no lift is nonempty.**
The image of the source is closed and misses the point, so the point has an open neighbourhood
over which the base change is empty, and the sheaf has a section over that empty base change. -/
theorem nonempty_etaleStalk_pushforward_of_isEmpty_lifts_univ {X Y : B.Scheme} (k : X ⟶ Y)
    [IsIntegralHom (B.inclusion.map k)] (z : GeometricPoint Y.1)
    (hz : IsEmpty {a : z.source ⟶ X.1 // a ≫ B.inclusion.map k = z.hom})
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    Nonempty (etaleStalk B Y.1 Y.property z ((B.smallPushforward k _).obj F).obj) := by
  obtain ⟨O, hzO, hO⟩ :=
    _root_.AlgebraicGeometry.exists_open_base_of_geometricLifts_of_isIntegralHom
      (B.inclusion.map k) z ⊥ (fun a => (hz.false a).elim)
  have hsize : B.Contains O := (Scheme.size_coe_opens_le _ O).trans_lt Y.property
  let W : SmallEtale B Y.1 Y.property :=
    ⟨Over.mk (ObjectProperty.homMk O.ι : B.obj O hsize ⟶ Y), inferInstanceAs (Etale O.ι)⟩
  have hrange : Set.range z.hom ⊆ Set.range O.ι := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨z.hom a, by rwa [Subsingleton.elim a default]⟩, rfl⟩
  let w : (geometricPointFiber B Y.1 Y.property z).obj W :=
    ⟨IsOpenImmersion.lift O.ι z.hom hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hempty : IsEmpty ((SmallEtale.toScheme B X.1 X.property).obj
      ((smallEtaleBaseChange B k).obj W)) := by
    refine ⟨fun p => ?_⟩
    let p' : B.inclusion.obj (pullback W.obj.hom k) := p
    have hp : (B.inclusion.map (pullback.snd W.obj.hom k) ≫ B.inclusion.map k) p' ∈ O := by
      rw [← (isPullback_smallEtaleBaseChange_inclusion B k W).w, Scheme.Hom.comp_apply]
      exact (B.inclusion.map (pullback.fst W.obj.hom k) p').2
    exact hO (by rwa [Scheme.Hom.comp_apply] at hp)
  obtain ⟨s⟩ := nonempty_sections_of_isEmpty_univ B X.1 X.property F _ hempty
  exact ⟨colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property z)).op ⋙
    ((B.smallPushforward k _).obj F).obj)
    (op ((geometricPointFiber B Y.1 Y.property z).elementsMk W w)) s⟩

end Empty

section Stages

namespace SmallEtaleIntegralStages

variable {B} {X Y : B.Scheme} {f : X ⟶ Y} (P : SmallEtaleIntegralStages B f)

end SmallEtaleIntegralStages

end Stages

end AlgebraicGeometry
