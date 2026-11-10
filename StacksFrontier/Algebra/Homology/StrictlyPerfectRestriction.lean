module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximation

/-!
# Restricting sheaves of modules to an open, and lifting maps out of a finite free module

Let `(X, O_X)` be a ringed space and let `U` be an open of `X`. Restriction of sheaves of modules
along an open embedding gives a functor from `O_X`-modules to `O_{X|U}`-modules. A morphism
`α : E ⟶ F` of `O_X`-modules whose source is a direct summand of a finite free module factors,
locally on `X`, through any epimorphism `p : G ⟶ F`.

## Main definitions

* `Stacks.PresheafOfModules.sectionOfTop`: the section of a presheaf of modules on a space
  determined by an element of its sections over the whole space.
* `Stacks.SheafOfModules.restrictSheafOfRings`: the restriction of a sheaf of rings along an
  open embedding of topological spaces.
* `Stacks.SheafOfModules.restrictSheafOfModules`: restriction of sheaves of modules along an
  open embedding, as a functor to modules over the restricted sheaf of rings.
* `StrictlyPerfect.restrictModules`: the special case `O_X`-modules ⥤ `O_{X|U}`-modules, for
  `U` an open of a ringed space `X`.
* `StrictlyPerfect.restrictComplex`: the induced functor on cochain complexes.

## Main results

* `Stacks.PresheafOfModules.sections_ext_top`: a section of a presheaf of modules on a space
  is determined by its value on the whole space.
* `Stacks.SheafOfModules.exists_mem_exists_preimage_of_epi`: a section of the target of an
  epimorphism of sheaves of modules on a space lifts over some open neighbourhood of any
  given point.
* `Stacks.SheafOfModules.exists_mem_forall_exists_preimage_of_epi`: finitely many sections lift
  over one common open neighbourhood.
* `Stacks.SheafOfModules.exists_restrict_lift_unit`: finitely many morphisms out of the unit
  object lift through an epimorphism after restricting to a small enough open.
* `Stacks.SheafOfModules.exists_restrict_lift_of_retract`: a morphism out of a retract of a
  finite biproduct of copies of the unit object lifts through an epimorphism after
  restriction.
* `StrictlyPerfect.exists_local_lift_of_isDirectSummandOfFiniteFree`: a morphism of `O_X`-modules
  out of a direct summand of a finite free module factors, locally on `X`, through any epimorphism.

## References

* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Cohomology, Section 46](https://stacks.math.columbia.edu/tag/08C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite
open Stacks.SheafOfModules.EpiMono

universe w r t

namespace Stacks.PresheafOfModules

variable {Z : TopCat.{t}} {R : (Opens Z)ᵒᵖ ⥤ RingCat.{r}}

/-- The section of a presheaf of modules on a topological space determined by an element of its
sections over the whole space, by restricting that element to every open. -/
def sectionOfTop (M : _root_.PresheafOfModules.{w} R) (m : M.obj (op ⊤)) : M.sections :=
  M.sectionsMk (fun V => M.map (homOfLE le_top : V.unop ⟶ ⊤).op m) (fun {V W} f => by
    rw [← M.map_comp_apply]
    exact M.congr_map_apply (Subsingleton.elim _ _) m)

/-- The value of `sectionOfTop M m` on an open `V` is the restriction of `m` to `V`. -/
@[simp]
lemma sectionOfTop_val (M : _root_.PresheafOfModules.{w} R) (m : M.obj (op ⊤)) (V : Opens Z) :
    (sectionOfTop M m).val (op V) = M.map (homOfLE le_top : V ⟶ ⊤).op m :=
  rfl

/-- The value of `sectionOfTop M m` on the whole space is `m`. -/
@[simp]
lemma sectionOfTop_val_top (M : _root_.PresheafOfModules.{w} R) (m : M.obj (op ⊤)) :
    (sectionOfTop M m).val (op ⊤) = m := by
  rw [sectionOfTop_val, M.congr_map_apply (Subsingleton.elim _ (𝟙 (op (⊤ : Opens Z)))) m]
  simp

/-- A section of a presheaf of modules on a topological space is determined by its value on
the whole space. -/
lemma sections_ext_top {M : _root_.PresheafOfModules.{w} R} {s s' : M.sections}
    (h : s.val (op ⊤) = s'.val (op ⊤)) : s = s' := by
  refine _root_.PresheafOfModules.sections_ext _ _ fun V => ?_
  rw [← M.sections_property (f := (homOfLE le_top : V.unop ⟶ ⊤).op) s,
    ← M.sections_property (f := (homOfLE le_top : V.unop ⟶ ⊤).op) s', h]

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

open Stacks.PresheafOfModules

variable {Y Z : TopCat.{t}} {f : Z ⟶ Y} (hf : IsOpenEmbedding f)
  (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{r})

/-! ### Restriction along an open embedding of spaces -/

/-- The restriction of a sheaf of rings on `Y` along an open embedding `f : Z ⟶ Y`: the open
`V` of `Z` is sent to the sections over the open `f '' V` of `Y`. -/
def restrictSheafOfRings : Sheaf (Opens.grothendieckTopology Z) RingCat.{r} :=
  letI := hf.functor_isContinuous
  (hf.functor.sheafPushforwardContinuous RingCat.{r}
    (Opens.grothendieckTopology Z) (Opens.grothendieckTopology Y)).obj R

/-- Restriction of sheaves of modules along an open embedding `f : Z ⟶ Y`: the pushforward along
the continuous functor `V ↦ f '' V` of sites and the identity of `restrictSheafOfRings hf R`. -/
def restrictSheafOfModules :
    _root_.SheafOfModules.{w} R ⥤ _root_.SheafOfModules.{w} (restrictSheafOfRings hf R) :=
  letI := hf.functor_isContinuous
  _root_.SheafOfModules.pushforward (F := hf.functor) (𝟙 (restrictSheafOfRings hf R))

/-- Restriction of sheaves of modules along an open embedding is additive. -/
instance : (restrictSheafOfModules.{w} hf R).Additive where
  map_add := by intros; ext; rfl

/-! ### Lifting finitely many sections locally -/

/-- If a section `s` of the target of `p` lifts to `t` over `V`, it lifts to the restriction of `t`
over every smaller open `W`. -/
private theorem app_map_eq_of_app_eq {R' : Sheaf (Opens.grothendieckTopology Z) RingCat.{r}}
    {F G : _root_.SheafOfModules.{r} R'} (p : G ⟶ F)
    (s : F.sections) {V W : Opens Z} (f : W ⟶ V) (t : G.val.obj (op V))
    (h : p.val.app (op V) t = s.val (op V)) :
    p.val.app (op W) (G.val.map f.op t) = s.val (op W) :=
  (_root_.PresheafOfModules.naturality_apply p.val f.op t).trans
    ((congrArg _ h).trans (s.property _))

variable [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{r}]
  [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{r}]

variable {R' : Sheaf (Opens.grothendieckTopology Z) RingCat.{r}}

/-- A section of the target of an epimorphism of sheaves of modules on a topological space lifts
over some open neighbourhood of any given point. -/
theorem exists_mem_exists_preimage_of_epi {F G : _root_.SheafOfModules.{r} R'} (p : G ⟶ F)
    [Epi p] (s : F.sections) (x : Z) :
    ∃ V : Opens Z, x ∈ V ∧ ∃ t : G.val.obj (op V), p.val.app (op V) t = s.val (op V) := by
  obtain ⟨S, hS, hlift⟩ := exists_covering_of_epi p (V := ⊤) (s.val (op ⊤))
  obtain ⟨V, i, hi, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hS x (by trivial)
  obtain ⟨t, ht⟩ := hlift i hi
  exact ⟨V, hxV, t, ht.trans (s.property i.op)⟩

/-- Finitely many sections of the target of an epimorphism of sheaves of modules lift over one
common open neighbourhood of any given point. -/
theorem exists_mem_forall_exists_preimage_of_epi {F G : _root_.SheafOfModules.{r} R'}
    (p : G ⟶ F) [Epi p] {n : ℕ} (s : Fin n → F.sections) (x : Z) :
    ∃ V : Opens Z, x ∈ V ∧ ∀ k : Fin n, ∃ t : G.val.obj (op V),
      p.val.app (op V) t = (s k).val (op V) := by
  choose V hxV t ht using fun k : Fin n => exists_mem_exists_preimage_of_epi p (s k) x
  refine ⟨⨅ k, V k, ?_, fun k => ?_⟩
  · change (x : Z) ∈ (↑(⨅ k, V k) : Set Z)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxV
  · exact ⟨_, app_map_eq_of_app_eq p (s k) (homOfLE (iInf_le V k)) (t k) (ht k)⟩

/-- Finitely many morphisms out of the unit object lift through an epimorphism after restriction to
a small enough open. -/
theorem exists_restrict_lift_unit {F G : _root_.SheafOfModules.{r} R'} (p : G ⟶ F) [Epi p]
    {n : ℕ} (σ : Fin n → (_root_.SheafOfModules.unit R' ⟶ F)) (x : Z) :
    ∃ V : Opens Z, x ∈ V ∧ ∀ k : Fin n,
      ∃ τ : (restrictSheafOfModules.{r} V.isOpenEmbedding R').obj
            (_root_.SheafOfModules.unit R') ⟶
          (restrictSheafOfModules.{r} V.isOpenEmbedding R').obj G,
        τ ≫ (restrictSheafOfModules.{r} V.isOpenEmbedding R').map p =
          (restrictSheafOfModules.{r} V.isOpenEmbedding R').map (σ k) := by
  obtain ⟨V, hxV, hlift⟩ := exists_mem_forall_exists_preimage_of_epi p
    (fun k => F.unitHomEquiv (σ k)) x
  choose t ht using hlift
  have hle : V.isOpenEmbedding.functor.obj ⊤ ≤ V := (Opens.isOpenEmbedding_obj_top V).le
  set m : ∀ k : Fin n,
      ((restrictSheafOfModules.{r} V.isOpenEmbedding R').obj G).val.obj (op ⊤) :=
    fun k => G.val.map (homOfLE hle).op (t k) with hm
  refine ⟨V, hxV, fun k =>
    ⟨((restrictSheafOfModules.{r} V.isOpenEmbedding R').obj G).unitHomEquiv.symm
      (sectionOfTop _ (m k)), ?_⟩⟩
  refine (_root_.SheafOfModules.unitHomEquiv_symm_comp (sectionOfTop _ (m k))
    ((restrictSheafOfModules.{r} V.isOpenEmbedding R').map p)).trans
      ((Equiv.symm_apply_eq _).2 (sections_ext_top ?_))
  change p.val.app (op (V.isOpenEmbedding.functor.obj ⊤))
      ((sectionOfTop ((restrictSheafOfModules.{r} V.isOpenEmbedding R').obj G).val
        (m k)).val (op ⊤)) =
    (F.unitHomEquiv (σ k)).val (op (V.isOpenEmbedding.functor.obj ⊤))
  rw [sectionOfTop_val_top]
  exact app_map_eq_of_app_eq p (F.unitHomEquiv (σ k)) (homOfLE hle) (t k) (ht k)

variable [HasFiniteBiproducts (_root_.SheafOfModules.{r} R')]

/-- A morphism out of a retract of a finite biproduct of copies of the unit object lifts through an
epimorphism after restriction to a small enough open. -/
theorem exists_restrict_lift_of_retract {E F G : _root_.SheafOfModules.{r} R'} (p : G ⟶ F)
    [Epi p] {n : ℕ}
    (ρ : Retract E (⨁ fun _ : Fin n => _root_.SheafOfModules.unit R')) (α : E ⟶ F) (x : Z) :
    ∃ V : Opens Z, x ∈ V ∧
      ∃ β : (restrictSheafOfModules.{r} V.isOpenEmbedding R').obj E ⟶
          (restrictSheafOfModules.{r} V.isOpenEmbedding R').obj G,
        β ≫ (restrictSheafOfModules.{r} V.isOpenEmbedding R').map p =
          (restrictSheafOfModules.{r} V.isOpenEmbedding R').map α := by
  obtain ⟨V, hxV, hτ⟩ := exists_restrict_lift_unit p
    (fun k => biproduct.ι (fun _ : Fin n => _root_.SheafOfModules.unit R') k ≫ ρ.r ≫ α) x
  choose τ hτ using hτ
  refine ⟨V, hxV, (restrictSheafOfModules.{r} V.isOpenEmbedding R').map ρ.i ≫
    ∑ k : Fin n, (restrictSheafOfModules.{r} V.isOpenEmbedding R').map
      (biproduct.π (fun _ : Fin n => _root_.SheafOfModules.unit R') k) ≫ τ k, ?_⟩
  have htot : ∀ h : (⨁ fun _ : Fin n => _root_.SheafOfModules.unit R') ⟶ F,
      ∑ a : Fin n, biproduct.π (fun _ : Fin n => _root_.SheafOfModules.unit R') a ≫
        biproduct.ι (fun _ : Fin n => _root_.SheafOfModules.unit R') a ≫ h = h := by
    intro h
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp]
  rw [Category.assoc, Preadditive.sum_comp]
  simp only [Category.assoc, hτ, ← Functor.map_comp]
  rw [← Functor.map_sum, htot, ← Functor.map_comp, ← Category.assoc, ρ.retract,
    Category.id_comp]

end Stacks.SheafOfModules

namespace StrictlyPerfect

open Stacks.SheafOfModules

/-! ### Restriction of `O_X`-modules to an open subspace -/

/-- Restriction of `O_X`-modules to the open subspace `U` of a ringed space `X`, with values in the
modules on the ringed space `X.restrict U.isOpenEmbedding`. -/
def restrictModules (X : RingedSpace.{r, t}) (U : Opens X.carrier) :
    OXMod.{r, w, t} X ⥤ OXMod.{r, w, t} (X.restrict U.isOpenEmbedding) :=
  restrictSheafOfModules U.isOpenEmbedding (structureSheafOfRings X)

/-- Restriction of `O_X`-modules to an open subspace is additive. -/
instance (X : RingedSpace.{r, t}) (U : Opens X.carrier) : (restrictModules X U).Additive :=
  inferInstanceAs (restrictSheafOfModules U.isOpenEmbedding
    (structureSheafOfRings X)).Additive

/-- Restriction of a complex of `O_X`-modules to the open subspace `U`. -/
def restrictComplex {X : RingedSpace.{r, t}} (E : CochainComplex (OXMod.{r, w, t} X) ℤ)
    (U : Opens X.carrier) :
    CochainComplex (OXMod.{r, w, t} (X.restrict U.isOpenEmbedding)) ℤ :=
  ((restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

variable {X : RingedSpace.{r, t}}

/-- Restriction sends the structure sheaf, viewed as a module over itself, to the structure sheaf
of the open subspace. -/
lemma restrictModules_obj_structureModule (U : Opens X.carrier) :
    (restrictModules X U).obj (structureModule X) =
      structureModule (X.restrict U.isOpenEmbedding) :=
  rfl

/-! ### Lifting maps out of a direct summand of a finite free `O_X`-module -/

section RingedSpaceSpecialisation

variable {X : RingedSpace.{r, t}}
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{r}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Given `α : E ⟶ F` and an epimorphism `p : G ⟶ F` of `O_X`-modules with `E` a direct summand of
a finite free `O_X`-module, a factorisation of `α` through `p` exists locally on `X`: every point
has an open neighbourhood `U` and a morphism `β : E|_U ⟶ G|_U` with `β ≫ p|_U = α|_U`. -/
@[stacks 08C6 "module universe = ring universe, space universe free, stated through \
`restrictModules`. Strictly more general than the collapsed form in \
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StrictlyPerfectLift.lean`, strictly less \
than the arbitrary-module-universe form in `StrictlyPerfectLiftModuleUniverse.lean`."]
theorem exists_local_lift_of_isDirectSummandOfFiniteFree {E F G : OXMod.{r, r} X}
    (hE : IsDirectSummandOfFiniteFree E) (α : E ⟶ F) (p : G ⟶ F) [Epi p] (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : (restrictModules X U).obj E ⟶ (restrictModules X U).obj G,
        β ≫ (restrictModules X U).map p = (restrictModules X U).map α := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract E).mp hE
  exact exists_restrict_lift_of_retract p ρ α x

end RingedSpaceSpecialisation

end StrictlyPerfect

end
