module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLimits

/-!
# Finite local constancy along a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`. Restriction of sheaves along `G`
is then an equivalence of sheaf categories, and it preserves and reflects finite local constancy
of sheaves of sets.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_sheafPushforwardContinuous`: a sheaf of sets
  on `(D, K)` is finite locally constant exactly when its restriction to `(C, J)` is.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_iff_toEtaleSite`: the case of the
  size-bounded small étale site of Stacks 021B inside Mathlib's small étale site.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_abelian_iff_sheafPushforwardContinuous`,
  `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_abelian_iff_toEtaleSite` and
  `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_abelian_sheafEquiv_functor_iff`: the same
  for abelian sheaves, through their underlying sheaves of sets, and across
  `AlgebraicGeometry.SmallEtale.sheafEquiv`.

## Implementation notes

Both directions are statements about the trivializing sieves of
`Stacks.ConstantSheaf.finTrivSieve`. Over an object `Y` of `C`, the localization `Over.post G` of
`G` is again a dense subsite inclusion (`Stacks.Sites.overPost_isDenseSubsite`), so restriction
along it is an equivalence of the sheaf categories of the two slices which commutes with the
constant sheaf functors (`CategoryTheory.equivCommuteConstant`); and the restriction of the
localized sheaf `F|_{G Y}` along `Over.post G` is the localization at `Y` of the restricted sheaf,
on the nose. Hence `F` is constant with a finite value over `G Y` exactly when its restriction is
over `Y`. The covering conditions are then transported by the cover-lifting property of `G` in
one direction and by cover density in the other.

The file contains the sheaves-of-sets results together with their abelian versions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsDenseSubsite J K]

/-- The localization of the dense subsite inclusion at an object, as a local instance. -/
local instance isDenseSubsite_overPost (Y : C) :
    (Over.post (X := Y) G).IsDenseSubsite (J.over Y) (K.over (G.obj Y)) :=
  Stacks.Sites.overPost_isDenseSubsite G Y

/-- The terminal object of the slice of `D` over the image of `Y`, as the image of the terminal
object of the slice of `C` over `Y`. -/
noncomputable def overPostMkIdIsTerminal (Y : C) :
    IsTerminal ((Over.post (X := Y) G).obj (Over.mk (𝟙 Y))) :=
  (Over.mkIdTerminal (X := G.obj Y)).ofIso (Over.isoMk (Iso.refl _) (by
    change 𝟙 (G.obj Y) ≫ G.map (𝟙 Y) = 𝟙 (G.obj Y)
    simp))

/-- Restricting the localization of `F` at `G Y` along `Over.post G` is localizing the
restriction of `F` at `Y`: the two sheaves have the same underlying presheaf. -/
def overPullbackSheafPushforwardIso (Y : C) (F : Sheaf K (Type (max u v w))) :
    ((Over.post (X := Y) G).sheafPushforwardContinuous (Type (max u v w)) (J.over Y)
        (K.over (G.obj Y))).obj ((K.overPullback (Type (max u v w)) (G.obj Y)).obj F) ≅
      (J.overPullback (Type (max u v w)) Y).obj
        ((G.sheafPushforwardContinuous (Type (max u v w)) J K).obj F) :=
  Iso.refl _

/-- **Constancy with a finite value over a slice is transported by restriction along `G`.** -/
theorem isConstantFiniteOver_sheafPushforwardContinuous_iff (Y : C)
    (F : Sheaf K (Type (max u v w))) :
    IsConstantFiniteOver.{v, u, w} J Y
        ((G.sheafPushforwardContinuous (Type (max u v w)) J K).obj F) ↔
      IsConstantFiniteOver.{v, u, w} K (G.obj Y) F := by
  let e := Functor.IsDenseSubsite.sheafEquiv (J.over Y) (K.over (G.obj Y)) (Over.post (X := Y) G)
    (Type (max u v w))
  have hc := equivCommuteConstant (J.over Y) (Type (max u v w)) (K.over (G.obj Y))
    (Over.post (X := Y) G) (Over.mkIdTerminal (X := Y)) (overPostMkIdIsTerminal G Y)
  have hc' := equivCommuteConstant' (J.over Y) (Type (max u v w)) (K.over (G.obj Y))
    (Over.post (X := Y) G) (Over.mkIdTerminal (X := Y)) (overPostMkIdIsTerminal G Y)
  constructor
  · rintro ⟨E, hE, ⟨φ⟩⟩
    exact ⟨E, hE, ⟨(hc.app E).symm ≪≫ e.functor.mapIso
      (φ ≪≫ (overPullbackSheafPushforwardIso G Y F).symm) ≪≫ e.counitIso.app _⟩⟩
  · rintro ⟨E, hE, ⟨φ⟩⟩
    exact ⟨E, hE, ⟨hc'.app E ≪≫ e.inverse.mapIso φ ≪≫ overPullbackSheafPushforwardIso G Y F⟩⟩

/-- **Finite local constancy is detected on a dense subsite.** A sheaf of sets on `(D, K)` is
finite locally constant exactly when its restriction along the dense subsite inclusion `G` is. -/
theorem isFiniteLocallyConstant_iff_sheafPushforwardContinuous (F : Sheaf K (Type (max u v w))) :
    IsFiniteLocallyConstant K F ↔
      IsFiniteLocallyConstant J ((G.sheafPushforwardContinuous (Type (max u v w)) J K).obj F) := by
  have : G.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K G
  rw [isFiniteLocallyConstant_iff_trivSieve_mem.{v, u, w} K,
    isFiniteLocallyConstant_iff_trivSieve_mem.{v, u, w} J]
  constructor
  · intro hF U
    exact J.superset_covering
      (fun W _ hg ↦ (isConstantFiniteOver_sheafPushforwardContinuous_iff G W F).2 hg)
      (G.cover_lift J K (hF (G.obj U)))
  · intro hF V
    have himage : ∀ W : C, finTrivSieve.{v, u, w} K F (G.obj W) ∈ K (G.obj W) := by
      intro W
      refine K.superset_covering ?_ ((G.functorPushforward_mem_iff J K).2 (hF W))
      rintro Z h ⟨W', g, k, hg, rfl⟩
      exact ((isConstantFiniteOver_sheafPushforwardContinuous_iff G W' F).1 hg).restrict K k
    refine K.transitive (G.is_cover_of_isCoverDense K V) _ ?_
    rintro Z f ⟨⟨W, lift, _, _⟩⟩
    exact K.superset_covering (fun _ _ hh ↦ hh) (K.pullback_stable lift (himage W))

/-- **Finite local constancy of abelian sheaves is detected on a dense subsite.** An abelian
sheaf on `(D, K)` is finite locally constant exactly when its restriction along the dense subsite
inclusion `G` is: both conditions are conditions on the underlying sheaves of sets, and
restriction commutes with taking underlying sheaves of sets. -/
theorem isFiniteLocallyConstant_abelian_iff_sheafPushforwardContinuous
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{max u v}]
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    IsFiniteLocallyConstant K F ↔
      IsFiniteLocallyConstant J
        ((G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).obj F) := by
  rw [isFiniteLocallyConstant_iff_forget K, isFiniteLocallyConstant_iff_forget J]
  exact isFiniteLocallyConstant_iff_sheafPushforwardContinuous.{max u v} G _

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.SmallEtale

/-- **Finite local constancy is the same on the two small étale sites.** A sheaf of sets on
Mathlib's small étale site of `S` is finite locally constant exactly when its restriction to the
size-bounded small étale site of Stacks 021B is. -/
theorem isFiniteLocallyConstant_iff_toEtaleSite (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant S.smallEtaleTopology F ↔
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS)
        (((SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS) S.smallEtaleTopology).obj F) :=
  Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_sheafPushforwardContinuous.{u + 1}
    (SmallEtale.toEtaleSite B S hS) F

/-- **Finite local constancy of abelian sheaves is the same on the two small étale sites.** An
abelian sheaf on Mathlib's small étale site of `S` is finite locally constant exactly when its
restriction to the size-bounded small étale site of Stacks 021B is. -/
theorem isFiniteLocallyConstant_abelian_iff_toEtaleSite (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant S.smallEtaleTopology F ↔
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS)
        (((SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS) S.smallEtaleTopology).obj F) :=
  Stacks.ConstantSheaf.isFiniteLocallyConstant_abelian_iff_sheafPushforwardContinuous
    (SmallEtale.toEtaleSite B S hS) F

/-- **Finite local constancy across the equivalence of the two small étale sites.** A sheaf on
the size-bounded small étale site of Stacks 021B is finite locally constant exactly when the
corresponding sheaf on Mathlib's small étale site is. -/
theorem isFiniteLocallyConstant_abelian_sheafEquiv_functor_iff (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant S.smallEtaleTopology
        ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).functor.obj F) ↔
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F := by
  rw [isFiniteLocallyConstant_abelian_iff_toEtaleSite B S hS]
  exact ⟨fun h ↦ Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
      ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).unitIso.app F).symm (hF := h),
    fun h ↦ Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
      ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).unitIso.app F) (hF := h)⟩

end AlgebraicGeometry.SmallEtale
