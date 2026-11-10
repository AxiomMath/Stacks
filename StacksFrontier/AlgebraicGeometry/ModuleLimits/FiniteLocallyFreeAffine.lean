module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Descent of finite locally free modules through a limit of schemes which is affine

Let `S = lim Sᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated schemes
with affine transition morphisms.  [Stacks Project, Tag 0B8W] (1) asserts that every finite
locally free `𝒪_S`-module is the pullback of a finite locally free `𝒪_{Sᵢ}`-module for some
`i`, and
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso_of_eventually`
reduces that tag to the conjunction of Algebra, Lemmas 02JO and 00NX in the following form: a
sheaf of modules of finite presentation at a stage whose pullback to the limit is finite locally
free becomes finite locally free along some transition morphism.

This file proves that statement when every stage of the diagram is *affine*.  The reduction of
the general quasi-compact quasi-separated case to this one, by a finite affine open covering of
the stage, is
`StacksDraft.AlgebraicGeometry.F3b.ModuleLimits.FiniteLocallyFreeUnconditional`.

## Main results

* `Stacks.AlgebraicGeometry.AffineTilde.isFiniteLocallyFree_tildeOf_iff`: on an affine scheme,
  the sheaf associated with a module is finite locally free exactly when the module is.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_of_isLimit` and its
  universe-unrestricted form `..._of_isLimit'`: Tags 02JO and 00NX in the sheaf-level form the
  proof of Tag 0B8W (1) uses them, for a cofiltered diagram of affine schemes.

## Implementation notes

**Why affine.**  Finite local freeness of a sheaf of modules is a local condition, and the
module-theoretic input is available only over a ring: on an affine scheme a sheaf of modules of
finite presentation is the sheaf associated with a finitely presented module of global sections
(`Stacks.AlgebraicGeometry.AffineTilde.exists_iso_tildeOf`), its pullback along a morphism of
affine schemes is the sheaf associated with the base change of that module
(`Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIsoApp`, Tag 01I9), and global sections
turn the limit of a cofiltered diagram of affine schemes into a filtered colimit of rings.  The
general quasi-compact quasi-separated case of the tag needs in addition the reduction to a
finite affine open covering of the stage, over each member of which the diagram of preimages is
a cofiltered diagram of affine schemes with limit the corresponding open of the limit; that
reduction is carried out in the module named above.

**The finite-local-freeness predicate.**  As in
`StacksDraft.AlgebraicGeometry.F3b.ModuleLimits.FiniteLocallyFree`, the class used is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, the one in which
`AlgebraicGeometry.HasResolutionProperty` is stated.  The bridge to the pointwise form
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, in which the sheaf-to-module comparison
of Tag 05JM is available, is `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`.

**The index universes.**  The affine case runs the ring-level spreading-out argument, which
needs a directed partially ordered final model of the index category and so needs the index
objects and morphisms to live in the universe of the schemes.  The statements therefore come in
two forms, the second obtained from the first by replacing the index category with
`CategoryTheory.Functor.FullImage D`, exactly as for Tag 01ZR in
`StacksDraft.AlgebraicGeometry.F3b.ModuleLimits.MapDescentHmap`.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe v u

namespace Stacks.AlgebraicGeometry.AffineTilde

/-- Finite local freeness of a sheaf of modules is invariant under isomorphism. -/
private theorem isFiniteLocallyFree_congr {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M ↔
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
  ⟨fun h => SheafOfModules.IsFiniteLocallyFree.of_iso (h := h) e,
    fun h => SheafOfModules.IsFiniteLocallyFree.of_iso (h := h) e.symm⟩

/-- On an affine scheme, the sheaf associated with a module is finite locally free exactly when
the module is. -/
theorem isFiniteLocallyFree_tildeOf_iff (X : Scheme.{u}) [IsAffine X] (M : ModuleCat.{u} Γ(X, ⊤)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((tildeOf X).obj M) ↔
      Module.IsFiniteLocallyFree Γ(X, ⊤) M := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback X.isoSpec.inv).obj ((tildeOf X).obj M)) :=
      SheafOfModules.IsFiniteLocallyFree.pullback_scheme X.isoSpec.inv _ h
    have e : (Scheme.Modules.pullback X.isoSpec.inv).obj ((tildeOf X).obj M) ≅
        AlgebraicGeometry.tilde (R := Γ(X, ⊤)) M :=
      (Scheme.Modules.pullbackComp X.isoSpec.inv X.isoSpec.hom).app _ ≪≫
        (Scheme.Modules.pullbackCongr X.isoSpec.inv_hom_id).app _ ≪≫
        (Scheme.Modules.pullbackId _).app _
    exact (tilde_isFiniteLocallyFree_iff Γ(X, ⊤) M).mp
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr
        ((isFiniteLocallyFree_congr e).mp h1))
  · exact SheafOfModules.IsFiniteLocallyFree.pullback_scheme X.isoSpec.hom _
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mp
        ((tilde_isFiniteLocallyFree_iff Γ(X, ⊤) M).mpr h))

/-- For a morphism of affine schemes, the pullback of the sheaf associated with a module is
finite locally free exactly when the base change of the module is. -/
theorem isFiniteLocallyFree_pullback_tildeOf_iff {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : ModuleCat.{u} Γ(Y, ⊤)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Scheme.Modules.pullback f).obj ((tildeOf Y).obj M)) ↔
      Module.IsFiniteLocallyFree Γ(X, ⊤) ((ModuleCat.extendScalars f.appTop.hom).obj M) :=
  (isFiniteLocallyFree_congr (tildeOfPullbackIsoApp f M)).trans
    (isFiniteLocallyFree_tildeOf_iff X _)

end Stacks.AlgebraicGeometry.AffineTilde

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Stacks.AlgebraicGeometry.AffineTilde

section AffineDiagram

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ i, IsAffine (D.obj i)] (c : Cone D)

include c in
/-- **Tags 02JO and 00NX for sheaves of modules on a cofiltered limit of affine schemes.**  Let
`c` be a limit cone on a cofiltered diagram `D` of affine schemes, let `Eᵢ` be a sheaf of
modules of finite presentation on a stage, and suppose its pullback to the limit is finite
locally free.  Then its pullback along some transition morphism is already finite locally free.

This is the hypothesis `hEventuallyFiniteLocallyFree` of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso_of_eventually`,
for a diagram of affine schemes.  Everything is read off on global sections: `Eᵢ` is the sheaf
associated with a finitely presented module `M` over `Γ(D.obj i, ⊤)`, the global sections of
the limit are the filtered colimit of the global sections of the stages, and the pullbacks of
`Eᵢ` are the sheaves associated with the base changes of `M`.  Finite local freeness of a
module is finiteness together with projectivity, and projectivity spreads out from the colimit
to a stage by `Stacks.RingFilteredColimits.exists_projective_tensor_of_isColimit`. -/
theorem exists_isFiniteLocallyFree_pullback_of_isLimit (hc : IsLimit c) (i : I)
    (Eᵢ : (D.obj i).Modules) [Eᵢ.IsFinitePresentation]
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ)) :
    ∃ (j : I) (e : j ⟶ i), SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (D.map e)).obj Eᵢ) := by
  have hca : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hcai : IsAffine (((Functor.const I).obj c.pt).obj i) := hca
  have haff : ∀ k : Over i, IsAffine ((Over.forget i ⋙ D).obj k) := fun k =>
    inferInstanceAs (IsAffine (D.obj k.left))
  set D' : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  set c' : Cone D' := c.whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have hop : ∀ j, IsAffine (D'.op.obj j).unop := by
    dsimp
    infer_instance
  set G : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := D'.op ⋙ Scheme.Γ
  set d : Cocone G := Scheme.Γ.mapCocone c'.op
  have hd : IsColimit d := isColimitOfPreserves Scheme.Γ hc'.op
  have hterm : IsTerminal (Over.mk (𝟙 i)) := Over.mkIdTerminal
  set l₀ : (Over i)ᵒᵖ := Opposite.op (Over.mk (𝟙 i))
  let ιmap : ∀ l : (Over i)ᵒᵖ, l₀ ⟶ l :=
    fun l => (Over.homMk l.unop.hom : l.unop ⟶ Over.mk (𝟙 i)).op
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(D.obj i, ⊤) (G.obj l) :=
    fun l => ((D.map l.unop.hom).appTop).hom.toAlgebra
  let _ : Algebra Γ(D.obj i, ⊤) d.pt := ((c.π.app i).appTop).hom.toAlgebra
  have hιcomp : ∀ {l m : (Over i)ᵒᵖ} (e : l ⟶ m), ιmap l ≫ e = ιmap m := fun {_ _} _ =>
    Quiver.Hom.unop_inj (hterm.hom_ext _ _)
  have haR : ∀ (l : (Over i)ᵒᵖ) (x : Γ(D.obj i, ⊤)),
      d.ι.app l (algebraMap Γ(D.obj i, ⊤) (G.obj l) x) = algebraMap Γ(D.obj i, ⊤) d.pt x := by
    intro l x
    change (G.map (ιmap l) ≫ d.ι.app l) x = d.ι.app l₀ x
    rw [d.w]
  have ha : ∀ {l m : (Over i)ᵒᵖ} (e : l ⟶ m) (x : Γ(D.obj i, ⊤)),
      G.map e (algebraMap Γ(D.obj i, ⊤) (G.obj l) x)
        = algebraMap Γ(D.obj i, ⊤) (G.obj m) x := by
    intro l m e x
    change (G.map (ιmap l) ≫ G.map e) x = G.map (ιmap m) x
    rw [← G.map_comp, hιcomp e]
  obtain ⟨M, hMfp, ⟨eE⟩⟩ := exists_iso_tildeOf (D.obj i) Eᵢ
  have hM : Module.FinitePresentation Γ(D.obj i, ⊤) M := hMfp
  have h3 := (isFiniteLocallyFree_pullback_tildeOf_iff (c.π.app i) M).mp
    ((isFiniteLocallyFree_congr ((Scheme.Modules.pullback (c.π.app i)).mapIso eE)).mpr hflf)
  have h4 : Module.Projective d.pt (d.pt ⊗[Γ(D.obj i, ⊤)] M) :=
    ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mp h3).2
  obtain ⟨l, hl⟩ := Stacks.RingFilteredColimits.exists_projective_tensor_of_isColimit haR
    (fun {_ _} e x => ha e x) hd M
  refine ⟨l.unop.left, l.unop.hom, ?_⟩
  have h5 : Module.IsFiniteLocallyFree (G.obj l) (G.obj l ⊗[Γ(D.obj i, ⊤)] M) :=
    (Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨inferInstance, hl⟩
  exact (isFiniteLocallyFree_congr ((Scheme.Modules.pullback (D.map l.unop.hom)).mapIso eE)).mp
    ((isFiniteLocallyFree_pullback_tildeOf_iff (D.map l.unop.hom) M).mpr h5)

end AffineDiagram

section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ i, IsAffine (D.obj i)] (c : Cone D)

include c in
/-- `exists_isFiniteLocallyFree_pullback_of_isLimit` with the index morphism universe
unrestricted, obtained by replacing the index category with
`CategoryTheory.Functor.FullImage D`. -/
theorem exists_isFiniteLocallyFree_pullback_of_isLimit' (hc : IsLimit c) (i : I)
    (Eᵢ : (D.obj i).Modules) [Eᵢ.IsFinitePresentation]
    (hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (c.π.app i)).obj Eᵢ)) :
    ∃ (j : I) (e : j ⟶ i), SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (D.map e)).obj Eᵢ) := by
  have haff : ∀ j : FullImage D, IsAffine ((ι D).obj j) := fun j =>
    inferInstanceAs (IsAffine (D.obj j.as))
  have hfp2 : SheafOfModules.IsFinitePresentation
      (R := ((ι D).obj (⟨i⟩ : FullImage D)).ringCatSheaf) Eᵢ := ‹_›
  obtain ⟨j, gm, hj⟩ := exists_isFiniteLocallyFree_pullback_of_isLimit (ι D) (cone D c)
    (isLimitCone D hc) ⟨i⟩ Eᵢ hflf
  refine ⟨j.as, hom D gm, ?_⟩
  rwa [map_hom D gm]

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end
