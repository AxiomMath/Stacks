module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# Coarsening the topology on a sheaf of modules, and quasi-coherence

Fix a category `C` carrying two Grothendieck topologies with `J' ≤ J`, and a sheaf of rings `R`
for the finer topology `J`.  Then `R` is also a sheaf for `J'`, every `J`-sheaf of `R`-modules is
a `J'`-sheaf of modules with the *same* underlying presheaf of modules, and the resulting
comparison functor `SheafOfModules.ofLE` is fully faithful.  On the five sites associated with a
category fibred in groupoids (Stacks 06TP) this is the comparison between the fppf category of
modules and the Zariski, étale, smooth and syntomic ones.

The comparison functor has a left adjoint, `SheafOfModules.sheafifyOfLE`: a `J'`-sheaf of modules
is sent to the `J`-sheafification of its underlying presheaf of modules.  Because
`SheafOfModules.ofLE` is fully faithful, the counit of the adjunction is an isomorphism
(`SheafOfModules.sheafifyOfLEObjOfLEIso`).

Quasi-coherence passes from a coarser topology to a finer one: a sheaf of modules for `J` whose
underlying presheaf is quasi-coherent as a `J'`-sheaf of modules is quasi-coherent as a `J`-sheaf
of modules.  This is one direction of Stacks 0EM8, and it holds on an arbitrary site.

## Main definitions

* `CategoryTheory.Sheaf.ofLE`: a sheaf for a finer topology, read as a sheaf for a coarser one.
* `SheafOfModules.ofLE`: the induced fully faithful comparison of module categories.
* `SheafOfModules.sheafifyOfLE` and `SheafOfModules.sheafifyOfLEAdjunction`: its left adjoint and
  the adjunction.

## Main results

* `SheafOfModules.sheafifyOfLEObjOfLEIso`: the counit of the adjunction is an isomorphism.
* `SheafOfModules.HasGlobalPresentation.of_functor`: a global presentation is carried by any
  functor between categories of sheaves of modules on the same category of site objects that
  preserves colimits and zero morphisms and matches up the two structure sheaves.
* `SheafOfModules.HasGlobalPresentation.of_coarser` and
  `SheafOfModules.IsQuasicoherentOnSite.of_coarser`: a global presentation, respectively
  quasi-coherence, for a coarser topology gives one for a finer topology.
* `SheafOfModules.isQuasicoherentOnSite_of_coarser`: the same, with the sheafification hypotheses
  discharged for a site whose objects and morphisms lie below the universe of module sections.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace CategoryTheory

namespace Limits

/-- Reindexing a coproduct cofan along an isomorphism of the constant family. -/
noncomputable def isColimitCofanMkOfIso {C : Type u} [Category.{v} C] {I : Type t}
    {X Y P : C} (e : X ≅ Y) (ι : I → (Y ⟶ P)) (h : IsColimit (Cofan.mk P ι)) :
    IsColimit (Cofan.mk P (fun i ↦ e.hom ≫ ι i)) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc h (fun i ↦ e.inv ≫ s.inj i)) ?_ ?_
  · intro s i
    have hi : ι i ≫ Cofan.IsColimit.desc h (fun i ↦ e.inv ≫ s.inj i) = e.inv ≫ s.inj i :=
      Cofan.IsColimit.fac h _ i
    simp [hi]
  · intro s f hf
    refine Cofan.IsColimit.hom_ext h _ _ fun i ↦ ?_
    rw [Cofan.IsColimit.fac]
    simpa using congrArg (fun k ↦ e.inv ≫ k) (hf i)

end Limits

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}
  {A : Type*} [Category A]

/-- A sheaf for a topology is a sheaf for any coarser topology, with the same underlying
presheaf. -/
def ofLE (h : J' ≤ J) (F : Sheaf J A) : Sheaf J' A :=
  ⟨F.obj, F.property.of_le h⟩

/-- The underlying presheaf of `CategoryTheory.Sheaf.ofLE h F` is that of `F`. -/
@[simp] theorem ofLE_obj (h : J' ≤ J) (F : Sheaf J A) : (F.ofLE h).obj = F.obj := rfl

/-- Coarsening commutes with localization at an object. -/
theorem over_ofLE (h : J' ≤ J) (F : Sheaf J A) (X : C) :
    (F.ofLE h).over X = (F.over X).ofLE (GrothendieckTopology.over_mono h X) := rfl

end Sheaf

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}

section

variable (h : J' ≤ J) (R : Sheaf J RingCat.{r})

/-- A sheaf of modules for a topology, read as a sheaf of modules for a coarser topology.  The
underlying presheaf of modules is unchanged. -/
def ofLE : SheafOfModules.{m} R ⥤ SheafOfModules.{m} (R.ofLE h) where
  obj M := ⟨M.val, M.isSheaf.of_le h⟩
  map f := ⟨f.val⟩

/-- The underlying presheaf of modules of `(SheafOfModules.ofLE h R).obj M` is that of `M`. -/
@[simp] theorem ofLE_obj_val (M : SheafOfModules.{m} R) :
    ((ofLE.{u, v, r, m} h R).obj M).val = M.val := rfl

/-- The underlying morphism of `(SheafOfModules.ofLE h R).map f` is that of `f`. -/
@[simp] theorem ofLE_map_val {M N : SheafOfModules.{m} R} (f : M ⟶ N) :
    ((ofLE.{u, v, r, m} h R).map f).val = f.val := rfl

/-- `SheafOfModules.ofLE` is fully faithful. -/
def fullyFaithfulOfLE : (ofLE.{u, v, r, m} h R).FullyFaithful where
  preimage f := ⟨f.val⟩

/-- `SheafOfModules.ofLE` is full. -/
instance : (ofLE.{u, v, r, m} h R).Full := (fullyFaithfulOfLE h R).full

/-- `SheafOfModules.ofLE` is faithful. -/
instance : (ofLE.{u, v, r, m} h R).Faithful := (fullyFaithfulOfLE h R).faithful

/-- Coarsening does not change the underlying presheaf of modules. -/
theorem ofLE_comp_forget :
    ofLE.{u, v, r, m} h R ⋙ forget _ = forget R := rfl

/-- Coarsening commutes with localization at an object. -/
theorem over_ofLE_obj (M : SheafOfModules.{m} R) (X : C) :
    ((ofLE.{u, v, r, m} h R).obj M).over X =
      (ofLE (GrothendieckTopology.over_mono h X) (R.over X)).obj (M.over X) := rfl

/-- Coarsening commutes with the universe lift used by global presentations. -/
theorem uliftForPresentation_ofLE_obj (M : SheafOfModules.{m} R) :
    uliftForPresentation.{u, v, r, m, t} ((ofLE.{u, v, r, m} h R).obj M) =
      (ofLE h R).obj (uliftForPresentation.{u, v, r, m, t} M) := rfl

/-- Coarsening carries the structure sheaf to the structure sheaf. -/
theorem ofLE_obj_unit : (ofLE.{u, v, r, r} h R).obj (unit R) = unit (R.ofLE h) := rfl

/-- The underlying presheaf of modules of a sheaf of modules for the coarser topology, taken over
the ring sheaf for the finer topology: `SheafOfModules.forget` with its target written in terms of
`R` rather than `R.ofLE h`. -/
def forgetOfLE : SheafOfModules.{m} (R.ofLE h) ⥤ PresheafOfModules.{m} R.obj where
  obj M := M.val
  map f := f.val

/-- `SheafOfModules.forgetOfLE` is fully faithful. -/
def fullyFaithfulForgetOfLE : (forgetOfLE.{u, v, r, m} h R).FullyFaithful where
  preimage f := ⟨f⟩

end

section

variable (h : J' ≤ J) (R : Sheaf J RingCat.{r})
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- The `J`-sheafification of a sheaf of modules for the coarser topology `J'`.  This is the left
adjoint of `SheafOfModules.ofLE`. -/
noncomputable def sheafifyOfLE :
    SheafOfModules.{m} (R.ofLE h) ⥤ SheafOfModules.{m} R :=
  forgetOfLE h R ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

/-- Sheafifying for the finer topology is left adjoint to reading a sheaf of modules for the
coarser topology. -/
noncomputable def sheafifyOfLEAdjunction :
    sheafifyOfLE.{u, v, r, m} h R ⊣ ofLE.{u, v, r, m} h R :=
  Adjunction.restrictFullyFaithful
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))
    (fullyFaithfulForgetOfLE h R)
    (Functor.FullyFaithful.id _)
    (Iso.refl (forgetOfLE.{u, v, r, m} h R ⋙ PresheafOfModules.sheafification (𝟙 R.obj)))
    (Iso.refl (forget.{m} R))

/-- `SheafOfModules.sheafifyOfLE` is a left adjoint. -/
instance : (sheafifyOfLE.{u, v, r, m} h R).IsLeftAdjoint :=
  (sheafifyOfLEAdjunction h R).isLeftAdjoint

/-- The counit of `SheafOfModules.sheafifyOfLEAdjunction` is an isomorphism: a sheaf of modules for
the finer topology is its own `J`-sheafification. -/
noncomputable def sheafifyOfLEObjOfLEIso (M : SheafOfModules.{m} R) :
    (sheafifyOfLE.{u, v, r, m} h R).obj ((ofLE.{u, v, r, m} h R).obj M) ≅ M :=
  asIso ((sheafifyOfLEAdjunction h R).counit.app M)

end

/-- A global presentation is carried along any functor between categories of sheaves of modules on
one and the same category of site objects which preserves colimits and zero morphisms, matches the
two structure sheaves, and takes the given module to the given module. -/
theorem HasGlobalPresentation.of_functor {J J' : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {S : Sheaf J' RingCat.{r}}
    {M : SheafOfModules.{m} S} {N : SheafOfModules.{m} R}
    (H : SheafOfModules.{max u v r m} S ⥤ SheafOfModules.{max u v r m} R)
    [PreservesColimitsOfSize.{max u v r m, max u v r m} H] [H.PreservesZeroMorphisms]
    (e : uliftForPresentation.{u, v, r, r, max u v m} (unit R) ≅
      H.obj (uliftForPresentation.{u, v, r, r, max u v m} (unit S)))
    (eM : H.obj (uliftForPresentation.{u, v, r, m, max u v r} M) ≅
      uliftForPresentation.{u, v, r, m, max u v r} N)
    (hM : M.HasGlobalPresentation) : N.HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, hc⟩ := hM
  have hab' : H.map a ≫ H.map b ≫ eM.hom = 0 := by
    rw [← Category.assoc, ← H.map_comp, hab, H.map_zero, zero_comp]
  refine ⟨I, K, H.obj P, H.obj Q,
    fun i ↦ e.hom ≫ H.map (ι i), fun i ↦ e.hom ≫ H.map (κ i), ?_, ?_,
    H.map a, H.map b ≫ eM.hom, hab', ?_⟩
  iterate 2 exact ⟨isColimitCofanMkOfIso e _ ((isColimitMapCoconeCofanMkEquiv H _ _)
      (isColimitOfPreserves H (by assumption)))⟩
  · exact ⟨((isColimitMapCoconeCoforkEquiv' H hab)
      (isColimitOfPreserves H hc.some)).ofIsoColimit (Cofork.ext eM (by rfl))⟩

section

variable {h : J' ≤ J} {R : Sheaf J RingCat.{r}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v r m}]

/-- A global presentation for a coarser topology is a global presentation for a finer one. -/
theorem HasGlobalPresentation.of_coarser {M : SheafOfModules.{m} R}
    (hM : ((ofLE.{u, v, r, m} h R).obj M).HasGlobalPresentation) : M.HasGlobalPresentation := by
  exact HasGlobalPresentation.of_functor (M := (ofLE.{u, v, r, m} h R).obj M) (N := M)
    (sheafifyOfLE.{u, v, r, max u v r m} h R)
    (sheafifyOfLEObjOfLEIso.{u, v, r, max u v r m} h R
      (uliftForPresentation.{u, v, r, r, max u v m} (unit R))).symm
    (sheafifyOfLEObjOfLEIso.{u, v, r, max u v r m} h R
      (uliftForPresentation.{u, v, r, m, max u v r} M)) hM

end

/-- Quasi-coherence of a sheaf of modules for a coarser topology implies quasi-coherence for a
finer one.  On the five sites of Stacks 06TP this is the implication from the Zariski, étale,
smooth or syntomic condition to the fppf condition in Stacks 0EM8. -/
theorem IsQuasicoherentOnSite.of_coarser {h : J' ≤ J} {R : Sheaf J RingCat.{r}}
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r m}]
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v r m}]
    {M : SheafOfModules.{m} R}
    (hM : ((ofLE.{u, v, r, m} h R).obj M).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpresentation⟩ := hM.locally_hasGlobalPresentation U
    exact ⟨I, V, f, h _ hcover, fun i ↦
      HasGlobalPresentation.of_coarser (h := GrothendieckTopology.over_mono h (V i))
        (hpresentation i)⟩

/-- Quasi-coherence of a sheaf of modules for a coarser topology implies quasi-coherence for a
finer one, when the universe of the module sections contains those of the objects and the
morphisms of the site. -/
theorem isQuasicoherentOnSite_of_coarser (h : J' ≤ J) {R : Sheaf J RingCat.{r}}
    {M : SheafOfModules.{max u v r m} R}
    (hM : ((ofLE.{u, v, r, max u v r m} h R).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  have : ∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v r m} := fun X ↦
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} (J.over X)).1
  have : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r m} := fun X ↦
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
      max u v, v} (J.over X)
  exact IsQuasicoherentOnSite.of_coarser hM

end SheafOfModules

end
